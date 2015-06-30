# Copyright (C) 2015 Hermes Systems
# All Rights Reserved.
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

from oslo_log import helpers as log_helpers
from oslo_log import log as logging
from ryu.base import app_manager
from ryu.controller import handler
from ryu.controller import ofp_event
from ryu.ofproto import ofproto_v1_3

from ryu.lib import dpid as dpid_lib
from ryu.lib.packet import ethernet
from ryu.lib.packet import packet
from ryu.lib.packet import vlan
from ryu.lib.packet import ipv4
from ryu.lib.packet import udp
from ryu.lib.packet import dhcp
from ryu.lib.packet import in_proto
from ryu.lib import addrconv
from ryu.lib.addresses import IPAddr, parse_cidr
from ryu.ofproto import ether
from ryu.ofproto import inet
import struct

LOG = logging.getLogger(__name__)


class AddressPool(object):
    """
    Superclass for DHCP address pools

    Note that it's just a subset of a list (thus, you can always just use
    a list as a pool).  The one exception is an optional "subnet_mask" hint.

    It probably makes sense to change this abstraction so that we can more
    easily return addresses from multiple ranges, and because some things
    (e.g., getitem) are potentially difficult to implement and not particularly
    useful (since we only need to remove a single item at a time).
    """

    def __init__(self):
        """
        Initialize this pool.
        """
        pass

    def __contains__(self, item):
        """
        Is this IPAddr in the pool?
        """
        return False

    def append(self, item):
        """
        Add this IP address back into the pool
        """
        pass

    def remove(self, item):
        """
        Remove this IPAddr from the pool
        """
        pass

    def __len__(self):
        """
        Returns number of IP addresses in the pool
        """
        return 0

    def __getitem__(self, index):
        """
        Get an IPAddr from the pool.

        Note that this will only be called with index = 0!
        """
        pass


class SimpleAddressPool(AddressPool):
    """
    Simple AddressPool for simple subnet based pools.
    """

    def __init__(self, network="192.168.0.0/24", first=1, last=None,
                 count=None):
        """
        Simple subnet-based address pool

        Allocates count IP addresses out of network/network_size, starting
        with the first'th.  You may specify the end of the range with either
        last (to specify the last'th address to use) or count to specify the
        number to use.  If both are None, use up to the end of all
        legal addresses.

        Example for all of 192.168.x.x/16:
          SimpleAddressPool("192.168.0.0/16", 1, 65534)
        """
        network, network_size = parse_cidr(network)

        self.first = first
        self.network_size = network_size
        self.host_size = 32 - network_size
        self.network = IPAddr(network)

        if last is None and count is None:
            self.last = (1 << self.host_size) - 2
        elif last is not None:
            self.last = last
        elif count is not None:
            self.last = self.first + count - 1
        else:
            raise RuntimeError("Cannot specify both last and count")

        self.removed = set()

        if self.count <= 0: raise RuntimeError("Bad first/last range")
        if first == 0: raise RuntimeError("Can't allocate 0th address")
        if self.host_size < 0 or self.host_size > 32:
            raise RuntimeError("Bad network")
        if IPAddr(self.last | self.network.toUnsigned()) not in self:
            raise RuntimeError("Bad first/last range")

    def __repr__(self):
        return str(self)

    def __str__(self):
        t = self.network.toUnsigned()
        t = (IPAddr(t | self.first), IPAddr(t | self.last))
        return "<Addresses from %s to %s>" % t

    @property
    def subnet_mask(self):
        return IPAddr(((1 << self.network_size) - 1) << self.host_size)

    @property
    def count(self):
        return self.last - self.first + 1

    def __contains__(self, item):
        item = IPAddr(item)
        if item in self.removed: return False
        n = item.toUnsigned()
        mask = (1 << self.host_size) - 1
        nm = (n & mask) | self.network.toUnsigned()
        if nm != n: return False
        if (n & mask) == mask:
            return False
        if (n & mask) < self.first:
            return False
        if (n & mask) > self.last:
            return False
        return True

    def append(self, item):
        item = IPAddr(item)
        if item not in self.removed:
            if item in self:
                raise RuntimeError("%s is already in this pool" % (item,))
            else:
                raise RuntimeError("%s does not belong in this pool" % (item,))
        self.removed.remove(item)

    def remove(self, item):
        item = IPAddr(item)
        if item not in self:
            raise RuntimeError("%s not in this pool" % (item,))
        self.removed.add(item)

    def __len__(self):
        return (self.last - self.first + 1) - len(self.removed)

    def __getitem__(self, index):
        if index < 0:
            raise RuntimeError("Negative indices not allowed")
        if index >= len(self):
            raise IndexError("Item does not exist")
        c = self.first

        # Use a heuristic to find the first element faster (we hope)
        # Note this means that removing items changes the order of
        # our "list".
        c += len(self.removed)
        while c > self.last:
            c -= self.count

        while True:
            addr = IPAddr(c | self.network.toUnsigned())
            if addr not in self.removed:
                assert addr in self
            index -= 1
            if index < 0:
                return addr
            c += 1
            if c > self.last:
                c -= self.count


class Dhcpd(app_manager.RyuApp):
    _DHCP_CLIENT_PORT = 68
    _DHCP_SERVER_PORT = 67
    _MSG_TYPE_BOOT_REPLY = 2
    _MSG_TYPE_BOOT_REQ = 1
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]

    def __init__(self, ip_address="192.168.0.254", router_address=(), dns_address=(), pool=None, subnet=None,
                 install_flow=True):
        super(Dhcpd, self).__init__()

        def fix_addr(addr, backup):
            if addr is None:
                return None
            if addr is ():
                return IPAddr(backup)
            return IPAddr(addr)

        self._install_flow = install_flow

        self.ip_addr = IPAddr(ip_address)
        self.router_addr = fix_addr(router_address, ip_address)
        self.dns_addr = fix_addr(dns_address, self.router_addr)

        if pool is None:
            self.pool = [IPAddr("192.168.0." + str(x)) for x in range(100, 199)]
            self.subnet = IPAddr(subnet or "255.255.255.0")
        else:
            self.pool = pool
            self.subnet = subnet
            if hasattr(pool, 'subnet_mask'):
                self.subnet = pool.subnet_mask
            if self.subnet is None:
                raise RuntimeError("You must specify a subnet mask or use a pool with a subnet hint")

        self.lease_time = 180  # An hour
        # TODO: Actually make them expire :)

        self.offers = {}  # Eth -> IP we offered
        self.leases = {}  # Eth -> IP we leased

        if self.ip_addr in self.pool:
            LOG.debug("Removing my own IP (%s) from address pool", self.ip_addr)
            self.pool.remove(self.ip_addr)

            # core.openflow.addListeners(self)

    def _get_pool(self):
        """
        Get an IP pool.  Return None to not issue an IP.  You should probably log this.
        """
        return self.pool

    def add_flow(self, datapath):
        ofproto = datapath.ofproto
        match = datapath.ofproto_parser.OFPMatch(eth_type=ether.ETH_TYPE_IP,
                                                 ip_proto=inet.IPPROTO_UDP,
                                                 udp_src=68,
                                                 udp_dst=67)
        actions = [datapath.ofproto_parser.OFPActionOutput(datapath.ofproto_parser.OFPP_CONTROLLER)]
        instructions = [datapath.ofproto_parser.OFPInstructionActions(
            ofproto.OFPIT_APPLY_ACTIONS, actions)]

        mod = datapath.ofproto_parser.OFPFlowMod(
            datapath=datapath, cookie=0, cookie_mask=0, table_id=0,
            command=ofproto.OFPFC_ADD, idle_timeout=0, hard_timeout=0,
            priority=1, buffer_id=ofproto.OFP_NO_BUFFER,
            flags=0, match=match, instructions=instructions)

        datapath.send_msg(mod)

    @log_helpers.log_method_call
    def _send_dhcp_reply(self, datapath, port, pkt):
        ofp = datapath.ofproto
        ofpp = datapath.ofproto_parser
        pkt.serialize()
        data = pkt.data
        actions = [ofpp.OFPActionOutput(port=port)]
        out = ofpp.OFPPacketOut(datapath=datapath,
                                buffer_id=ofp.OFP_NO_BUFFER,
                                in_port=ofp.OFPP_CONTROLLER,
                                actions=actions,
                                data=data)
        datapath.send_msg(out)

    @handler.set_ev_cls(ofp_event.EventOFPPacketIn, handler.MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        """Check a packet-in message.

           Build and output an dhcp reply if a packet-in message is
           an dhcp packet.
        """
        msg = ev.msg
        LOG.debug("packet-in msg %s", msg)
        datapath = msg.datapath
        port = msg.match['in_port']
        # NOTE: Ryu packet library can raise various exceptions on a corrupted packet.
        try:
            pkt = packet.Packet(msg.data)
        except Exception as e:
            LOG.debug("Unparsable packet: got exception %s", e)
            return
        LOG.debug("packet-in dpid %(dpid)s in_port %(port)s pkt %(pkt)s",
                  {'dpid': dpid_lib.dpid_to_str(datapath.id),
                   'port': port, 'pkt': pkt})

        pkt_ethernet = pkt.get_protocol(ethernet.ethernet)
        if not pkt_ethernet:
            LOG.debug("drop non-ethernet packet")
            return
        pkt_vlan = pkt.get_protocol(vlan.vlan)
        pkt_ip = pkt.get_protocol(ipv4.ipv4)
        if pkt_ip is None:
            return
        pkt_udp = pkt.get_protocol(udp.udp)
        if pkt_udp is None:
            return
        pkt_dhcp = pkt.get_protocol(dhcp.dhcp)
        if pkt_dhcp is None:
            LOG.debug("drop non-dhcp packet")
            return
        pool = self._get_pool()
        if pool is None:
            return
        self._respond_dhcp(datapath, port, pool, pkt_ethernet, pkt_vlan, pkt_ip, pkt_udp, pkt_dhcp)

    def _respond_dhcp(self, datapath, port, pool,
                      pkt_ethernet, pkt_vlan, pkt_ip, pkt_udp, pkt_dhcp):
        # DHCP message type code
        options = dict()
        for option in pkt_dhcp.options.option_list:
            options[option.tag] = option.value
        src = pkt_dhcp.chaddr

        # RESPONSE MSG
        pkt = packet.Packet()
        pkt.add_protocol(ethernet.ethernet(ethertype=pkt_ethernet.ethertype,
                                           dst=pkt_ethernet.src,
                                           src='00:00:00:00:00:00'))
        if pkt_vlan:
            pkt.add_protocol(vlan.vlan(cfi=pkt_vlan.cfi,
                                       ethertype=pkt_vlan.ethertype,
                                       pcp=pkt_vlan.pcp,
                                       vid=pkt_vlan.vid))
        pkt.add_protocol(ipv4.ipv4(src=pkt_ip.dst, dst=pkt_ip.src, proto=in_proto.IPPROTO_UDP))
        pkt.add_protocol(udp.udp(src_port=pkt_udp.dst_port, dst_port=pkt_udp.src_port))

        # DISCOVER MSG
        dhcp_msg_type = ord(options[dhcp.DHCP_MESSAGE_TYPE_OPT])
        if dhcp_msg_type == dhcp.DHCP_DISCOVER:
            msg_type = dhcp.DHCP_OFFER
            if src in self.leases:
                offer = self.leases[src]
                del self.leases[src]
                self.offers[src] = offer
            else:
                offer = self.offers.get(src)
                if offer is None:
                    if len(pool) == 0:
                        LOG.error("Out of IP addresses")
                        msg_type = dhcp.DHCP_NAK

                    offer = pool[0]
                    if dhcp.DHCP_REQUESTED_IP_ADDR_OPT in options:
                        wanted_ip = IPAddr(addrconv.ipv4.bin_to_text(options[dhcp.DHCP_REQUESTED_IP_ADDR_OPT].value))
                        if wanted_ip in pool:
                            offer = wanted_ip
                    pool.remove(offer)
                    self.offers[src] = offer
            wanted_opts = list()
            if dhcp.DHCP_PARAMETER_REQUEST_LIST_OPT in options:
                fmt = ""
                for i in options[dhcp.DHCP_PARAMETER_REQUEST_LIST_OPT]:
                    fmt += "s"
                wanted_opt_set = struct.unpack(fmt, options[dhcp.DHCP_PARAMETER_REQUEST_LIST_OPT])
                for i in wanted_opt_set:
                    wanted_opts.append(ord(i))
            # DHCP options tag code
            option_list = list()
            option_list.append(dhcp.option(dhcp.DHCP_MESSAGE_TYPE_OPT, chr(msg_type), length=1))
            if dhcp.DHCP_SUBNET_MASK_OPT in wanted_opts:
                option_list.append(dhcp.option(dhcp.DHCP_SUBNET_MASK_OPT,
                                               addrconv.ipv4.text_to_bin(self.subnet.toStr()),
                                               length=4))
            if dhcp.DHCP_GATEWAY_ADDR_OPT in wanted_opts and self.router_addr is not None:
                option_list.append(dhcp.option(dhcp.DHCP_GATEWAY_ADDR_OPT,
                                               addrconv.ipv4.text_to_bin(self.router_addr.toStr()),
                                               length=4))
            if dhcp.DHCP_DNS_SERVER_ADDR_OPT in wanted_opts and self.dns_addr is not None:
                option_list.append(dhcp.option(dhcp.DHCP_DNS_SERVER_ADDR_OPT,
                                               addrconv.ipv4.text_to_bin(self.dns_addr.toStr()),
                                               length=4))
            option_list.append(dhcp.option(dhcp.DHCP_IP_ADDR_LEASE_TIME_OPT,
                                           chr(self.lease_time),
                                           length=4))
            option_list.append(dhcp.option(dhcp.DHCP_RENEWAL_TIME_OPT, chr(self.lease_time / 2), length=4))
            option_list.append(dhcp.option(dhcp.DHCP_REBINDING_TIME_OPT, chr(self.lease_time * 7 / 8), length=4))
            resp_options = dhcp.options(option_list=option_list)
            pkt.add_protocol(dhcp.dhcp(op=self._MSG_TYPE_BOOT_REPLY, chaddr=pkt_dhcp.chaddr, options=resp_options,
                                       xid=pkt_dhcp.xid, ciaddr=pkt_dhcp.ciaddr, yiaddr=offer.toStr(),
                                       siaddr=self.ip_addr.toStr(), giaddr='0.0.0.0', sname='', boot_file=''))

        # REQUEST MSG
        if dhcp_msg_type == dhcp.DHCP_REQUEST:
            msg_type = dhcp.DHCP_OFFER
            if dhcp.DHCP_REQUESTED_IP_ADDR_OPT not in options:
                return
            wanted_ip = IPAddr(addrconv.ipv4.bin_to_text(options[dhcp.DHCP_REQUESTED_IP_ADDR_OPT]))
            got_ip = None
            if src in self.leases:
                if wanted_ip != self.leases[src]:
                    pool.append(self.leases[src])
                    del self.leases[src]
                else:
                    got_ip = self.leases[src]
            if got_ip is None:
                if src in self.offers:
                    if wanted_ip != self.offers[src]:
                        pool.append(self.offers[src])
                        del self.offers[src]
                else:
                    got_ip = self.offers[src]
            if got_ip is None:
                if wanted_ip in pool:
                    pool.remove(wanted_ip)
                    got_ip = wanted_ip
            if got_ip is None:
                LOG.warn("%s asked for un-offered %s", src, wanted_ip.toStr())
                msg_type = dhcp.DHCP_NAK
            wanted_opts = list()
            if dhcp.DHCP_PARAMETER_REQUEST_LIST_OPT in options:
                fmt = ""
                for i in options[dhcp.DHCP_PARAMETER_REQUEST_LIST_OPT]:
                    fmt += "s"
                wanted_opt_set = struct.unpack(fmt, options[dhcp.DHCP_PARAMETER_REQUEST_LIST_OPT])
                for i in wanted_opt_set:
                    wanted_opts.append(ord(i))
            # DHCP options tag code
            option_list = list()
            option_list.append(dhcp.option(dhcp.DHCP_MESSAGE_TYPE_OPT, chr(msg_type), length=1))
            if dhcp.DHCP_SUBNET_MASK_OPT in wanted_opts:
                option_list.append(dhcp.option(dhcp.DHCP_SUBNET_MASK_OPT,
                                               addrconv.ipv4.text_to_bin(self.subnet.toStr()),
                                               length=4))
            if dhcp.DHCP_GATEWAY_ADDR_OPT in wanted_opts and self.router_addr is not None:
                option_list.append(dhcp.option(dhcp.DHCP_GATEWAY_ADDR_OPT,
                                               addrconv.ipv4.text_to_bin(self.router_addr.toStr()),
                                               length=4))
            if dhcp.DHCP_DNS_SERVER_ADDR_OPT in wanted_opts and self.dns_addr is not None:
                option_list.append(dhcp.option(dhcp.DHCP_DNS_SERVER_ADDR_OPT,
                                               addrconv.ipv4.text_to_bin(self.dns_addr.toStr()),
                                               length=4))
            option_list.append(dhcp.option(dhcp.DHCP_IP_ADDR_LEASE_TIME_OPT,
                                           chr(self.lease_time),
                                           length=4))
            option_list.append(dhcp.option(dhcp.DHCP_RENEWAL_TIME_OPT, chr(self.lease_time / 2), length=4))
            option_list.append(dhcp.option(dhcp.DHCP_REBINDING_TIME_OPT, chr(self.lease_time * 7 / 8), length=4))
            resp_options = dhcp.options(option_list=option_list)
            pkt.add_protocol(dhcp.dhcp(op=self._MSG_TYPE_BOOT_REPLY, chaddr=pkt_dhcp.chaddr, options=resp_options,
                                       xid=pkt_dhcp.xid, ciaddr=pkt_dhcp.ciaddr, yiaddr=wanted_ip.toStr(),
                                       siaddr=self.ip_addr.toStr(), giaddr='0.0.0.0', sname='', boot_file=''))

        # RELEASE MSG
        if dhcp_msg_type == dhcp.DHCP_RELEASE:
            if self.leases.get(src).toStr() != pkt_dhcp.ciaddr:
                LOG.warn("%s tried to release unleased %s" % (src, pkt_dhcp.ciaddr))
                return
            del self.leases[src]
            pool.append(pkt_dhcp.ciaddr)
            LOG.info("%s released %s" % (src, pkt_dhcp.ciaddr))

        self._send_dhcp_reply(datapath, port, pkt)
        return True
