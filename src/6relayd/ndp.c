/**
 * Copyright (C) 2012-2013 Steven Barth <steven@midlink.org>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License v2 as published by
 * the Free Software Foundation.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 */

#include <arpa/inet.h>
#include <errno.h>
#include <net/ethernet.h>
#include <netinet/icmp6.h>
#include <netinet/ip6.h>
#include <netpacket/packet.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/socket.h>
#include <unistd.h>

#include "ndp.h"
#include "router.h"
#include <linux/filter.h>
#include <linux/rtnetlink.h>

#define RTPROT_6RELAYD 66

// NetlinkRecvBuffer: Preserve memory for avoiding out of memory on exit
// 32KB:
// https://www.kernel.org/doc/html/v6.6/userspace-api/netlink/intro.html#buffer-sizing
#define NETLINK_RECV_BUFFER_SIZE 32768
static char NetlinkRecvBuffer[NETLINK_RECV_BUFFER_SIZE];

static const struct relayd_config *config = NULL;

static void handle_solicit(void *addr, void *data, size_t len, struct relayd_interface *iface);
static void handle_rtnetlink(void *addr, void *data, size_t len, struct relayd_interface *iface);
static struct ndp_neighbor *find_neighbor(struct in6_addr *addr, bool strict);
static void modify_neighbor(struct in6_addr *addr, struct relayd_interface *iface, bool add);
static ssize_t ping6(struct in6_addr *addr, const struct relayd_interface *iface);

static struct list_head neighbors = LIST_HEAD_INIT(neighbors);
static size_t neighbor_count = 0;
static uint32_t rtnl_seqid = 0;

static int ping_socket = -1;
static struct relayd_event ndp_event_solicit = { -1, NULL, handle_solicit };
static struct relayd_event rtnl_event = { -1, NULL, handle_rtnetlink };

// Filter ICMPv6 messages of type neighbor soliciation
static struct sock_filter bpf[] = {
	BPF_STMT(BPF_LD | BPF_B | BPF_ABS, offsetof(struct ip6_hdr, ip6_nxt)),
	BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, IPPROTO_ICMPV6, 0, 3),
	BPF_STMT(BPF_LD | BPF_B | BPF_ABS, sizeof(struct ip6_hdr) + offsetof(struct icmp6_hdr, icmp6_type)),
	BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, ND_NEIGHBOR_SOLICIT, 0, 1),
	BPF_STMT(BPF_RET | BPF_K, 0xffffffff),
	BPF_STMT(BPF_RET | BPF_K, 0),
};
static const struct sock_fprog bpf_prog = { sizeof(bpf) / sizeof(*bpf), bpf };

int flush_route() {
	{ // Send request of route list

		struct nl_route {
			struct nlmsghdr nlmh;
			struct rtmsg rtm;
		} nl_route = { 0 };

		// NLMSGHDR: Netlink message header
		nl_route.nlmh.nlmsg_len = NLMSG_LENGTH(sizeof(struct rtmsg));
		nl_route.nlmh.nlmsg_type = RTM_GETROUTE;
		nl_route.nlmh.nlmsg_flags = NLM_F_REQUEST | NLM_F_DUMP;
		nl_route.nlmh.nlmsg_seq = ++rtnl_seqid;

		// RTMSG: Route message
		nl_route.rtm.rtm_family = AF_INET6;
		nl_route.rtm.rtm_table = RT_TABLE_MAIN;
		nl_route.rtm.rtm_protocol = RTPROT_6RELAYD;

		send(rtnl_event.socket, &nl_route, nl_route.nlmh.nlmsg_len, MSG_DONTWAIT);
	}

	ssize_t len;
	struct nlmsghdr *nlmh;
	struct iovec iov = { NetlinkRecvBuffer, NETLINK_RECV_BUFFER_SIZE };
	while(1) {
		// len = recv(rtnl_event.socket, NetlinkRecvBuffer,
		// NETLINK_RECV_BUFFER_SIZE, 0);
		struct msghdr mh = { 0, 0, &iov, 1, 0, 0, 0 };
		len = recvmsg(rtnl_event.socket, &mh, 0);
		if(len <= 0) {
			return -1;
		}

		if(mh.msg_flags & MSG_TRUNC) {
			printf("E: Netlink message is too large and truncated!\n");
			return -1;
		}

		for(nlmh = (struct nlmsghdr *) NetlinkRecvBuffer; NLMSG_OK(nlmh, len); nlmh = NLMSG_NEXT(nlmh, len)) {
			if(nlmh->nlmsg_type == NLMSG_DONE) {
				return 0;
			}

			struct rtmsg *rtm = (struct rtmsg *) NLMSG_DATA(nlmh);
			struct rtattr *rta = (struct rtattr *) RTM_RTA(rtm);

			if(rtm->rtm_protocol != RTPROT_6RELAYD) {
				continue;
			}

			// Change header and send back to kernel
			nlmh->nlmsg_type = RTM_DELROUTE;
			nlmh->nlmsg_flags = NLM_F_REQUEST;
			send(rtnl_event.socket, nlmh, nlmh->nlmsg_len, MSG_WAITALL);

			/*
				int rtl = RTM_PAYLOAD(nlmh);
				while (RTA_OK(rta, rtl)) {
					if (rta->rta_type == RTA_DST) {
						char dest[INET6_ADDRSTRLEN];
						inet_ntop(AF_INET6, RTA_DATA(rta), dest, sizeof(dest)); printf("I: Cleanup route: %s\n", dest);
					}
					rta = RTA_NEXT(rta, rtl);
				}
			*/
		}
	}
	return 0;
}

// Initialize NDP-proxy
int init_ndp_proxy(const struct relayd_config *relayd_config) {
	config = relayd_config;
	if(config->slavecount < 1) {
		return 0;
	}

	// Setup netlink socket
	if((rtnl_event.socket = relayd_open_rtnl_socket()) < 0) {
		return -1;
	}

	// Cleanup previous session
	flush_route();

	// Receive netlink neighbor and ip-address events
	uint32_t group = RTNLGRP_IPV6_IFADDR;
	setsockopt(rtnl_event.socket, SOL_NETLINK, NETLINK_ADD_MEMBERSHIP, &group, sizeof(group));
	group = RTNLGRP_IPV6_ROUTE;
	setsockopt(rtnl_event.socket, SOL_NETLINK, NETLINK_ADD_MEMBERSHIP, &group, sizeof(group));

	// Synthesize initial address events
	struct {
		struct nlmsghdr nh;
		struct ifaddrmsg ifa;
	} nl_route = {
		{ sizeof(nl_route), RTM_GETADDR, NLM_F_REQUEST | NLM_F_DUMP, ++rtnl_seqid, 0 },
		{ .ifa_family = AF_INET6 }
	};

	send(rtnl_event.socket, &nl_route, sizeof(nl_route), MSG_DONTWAIT);

	relayd_register_event(&rtnl_event);

	// Test if disabled
	if(!config->enable_ndp_relay || config->slavecount < 1) {
		return 0;
	}

	for(size_t i = 0; i < config->static_ndp_len; ++i) {
		struct ndp_neighbor *n = malloc(sizeof(*n));
		n->timeout = 0;

		char ipbuf[INET6_ADDRSTRLEN];
		char iface[16];

		if(sscanf(config->static_ndp[i], "%45s/%hhu:%15s", ipbuf, &n->len, iface) < 3 || n->len > 128 || inet_pton(AF_INET6, ipbuf, &n->addr) != 1 || !(n->iface = relayd_get_interface_by_name(iface))) {
			syslog(LOG_ERR, "Invalid static NDP-prefix %s", config->static_ndp[i]);
			return -1;
		}

		list_add(&n->head, &neighbors);
	}

	// Create socket for intercepting NDP
	int sock = socket(AF_PACKET, SOCK_DGRAM | SOCK_CLOEXEC | SOCK_NONBLOCK,
			  htons(ETH_P_ALL)); // ETH_P_ALL for ingress + egress
	if(sock < 0) {
		syslog(LOG_ERR, "Unable to open packet socket: %s", strerror(errno));
		return -1;
	}

	if(setsockopt(sock, SOL_SOCKET, SO_ATTACH_FILTER, &bpf_prog, sizeof(bpf_prog))) {
		syslog(LOG_ERR, "Failed to set BPF: %s", strerror(errno));
		return -1;
	}

	struct packet_mreq mreq = { config->master.ifindex, PACKET_MR_ALLMULTI, ETH_ALEN, { 0 } };
	setsockopt(sock, SOL_PACKET, PACKET_ADD_MEMBERSHIP, &mreq, sizeof(mreq));

	for(size_t i = 0; i < config->slavecount; ++i) {
		mreq.mr_ifindex = config->slaves[i].ifindex;
		setsockopt(sock, SOL_PACKET, PACKET_ADD_MEMBERSHIP, &mreq, sizeof(mreq));
	}

	ndp_event_solicit.socket = sock;
	relayd_register_event(&ndp_event_solicit);

	// Open ICMPv6 socket
	ping_socket = socket(AF_INET6, SOCK_RAW | SOCK_CLOEXEC, IPPROTO_ICMPV6);

	int val = 2;
	setsockopt(ping_socket, IPPROTO_RAW, IPV6_CHECKSUM, &val, sizeof(val));

	// This is required by RFC 4861
	val = 255;
	setsockopt(ping_socket, IPPROTO_IPV6, IPV6_MULTICAST_HOPS, &val, sizeof(val));
	setsockopt(ping_socket, IPPROTO_IPV6, IPV6_UNICAST_HOPS, &val, sizeof(val));

	// Filter all packages, we only want to send
	struct icmp6_filter filt;
	ICMP6_FILTER_SETBLOCKALL(&filt);
	setsockopt(ping_socket, IPPROTO_ICMPV6, ICMP6_FILTER, &filt, sizeof(filt));

	// Netlink socket, continued...
	group = RTNLGRP_NEIGH;
	setsockopt(rtnl_event.socket, SOL_NETLINK, NETLINK_ADD_MEMBERSHIP, &group, sizeof(group));

	// Synthesize initial neighbor events
	struct {
		struct nlmsghdr nh;
		struct ndmsg ndm;
	} req = {
		{ sizeof(req), RTM_GETNEIGH, NLM_F_REQUEST | NLM_F_DUMP, ++rtnl_seqid, 0 },
		    { .ndm_family = AF_INET6 }
	};

	send(rtnl_event.socket, &req, sizeof(req), MSG_DONTWAIT);

	return 0;
}

// Deinitialize NDP proxy
void deinit_ndp_proxy() {
	printf("I: Unregistering routes...\n");

	while(!list_empty(&neighbors)) {
		struct ndp_neighbor *c = list_first_entry(&neighbors, struct ndp_neighbor, head);
		modify_neighbor(&c->addr, c->iface, false);
	}

	flush_route();
}

// Send an ICMP-ECHO. This is less for actually pinging but for the
// neighbor cache to be kept up-to-date.
static ssize_t ping6(struct in6_addr *addr, const struct relayd_interface *iface) {
	struct sockaddr_in6 dest = { AF_INET6, 0, 0, *addr, 0 };
	struct icmp6_hdr echo = { .icmp6_type = ICMP6_ECHO_REQUEST };
	struct iovec iov = { &echo, sizeof(echo) };

	// Linux seems to not honor IPV6_PKTINFO on raw-sockets, so work around
	setsockopt(ping_socket, SOL_SOCKET, SO_BINDTODEVICE, iface->ifname, sizeof(iface->ifname));
	return relayd_forward_packet(ping_socket, &dest, &iov, 1, iface);
}

// Handle solicitations
static void handle_solicit(void *addr, void *data, size_t len, struct relayd_interface *iface) {
	struct ip6_hdr *ip6 = data;
	struct nd_neighbor_solicit *req = (struct nd_neighbor_solicit *) &ip6[1];
	struct sockaddr_ll *ll = addr;

	// Solicitation is for duplicate address detection
	bool ns_is_dad = IN6_IS_ADDR_UNSPECIFIED(&ip6->ip6_src);

	// Don't forward any non-DAD solicitation for external ifaces
	// TODO: check if we should even forward DADs for them
	if(iface->external && !ns_is_dad) {
		return;
	}

	if(len < sizeof(*ip6) + sizeof(*req)) {
		return; // Invalid reqicitation
	}

	if(IN6_IS_ADDR_LINKLOCAL(&req->nd_ns_target) || IN6_IS_ADDR_LOOPBACK(&req->nd_ns_target) || IN6_IS_ADDR_MULTICAST(&req->nd_ns_target)) {
		return; // Invalid target
	}

	char ipbuf[INET6_ADDRSTRLEN];
	inet_ntop(AF_INET6, &req->nd_ns_target, ipbuf, sizeof(ipbuf));
	syslog(LOG_NOTICE, "Got a NS for %s", ipbuf);

	uint8_t mac[6];
	relayd_get_interface_mac(iface->ifname, mac);
	if(!memcmp(ll->sll_addr, mac, sizeof(mac)) && ll->sll_pkttype != PACKET_OUTGOING) {
		return; // Looped back
	}

	time_t now = time(NULL);

	struct ndp_neighbor *n = find_neighbor(&req->nd_ns_target, false);
	if(n && (n->iface || abs(n->timeout - now) < 5)) {
		syslog(LOG_NOTICE, "%s is on %s", ipbuf, (n->iface) ? n->iface->ifname : "<pending>");
		if(!n->iface || n->iface == iface) {
			return;
		}

		// Found on other interface, answer with advertisement
		struct {
			struct nd_neighbor_advert body;
			struct nd_opt_hdr opt_ll_hdr;
			uint8_t mac[6];
		} advert = {
        .body =
            {
                .nd_na_hdr = {ND_NEIGHBOR_ADVERT, 0, 0, {{0}}},
                .nd_na_target = req->nd_ns_target,
            },
        .opt_ll_hdr = {ND_OPT_TARGET_LINKADDR, 1},
    };

		memcpy(advert.mac, mac, sizeof(advert.mac));
		advert.body.nd_na_flags_reserved = ND_NA_FLAG_ROUTER | ND_NA_FLAG_SOLICITED;

		struct sockaddr_in6 dest = { AF_INET6, 0, 0, ALL_IPV6_NODES, 0 };
		if(!ns_is_dad) { // If not DAD, then unicast to source
			dest.sin6_addr = ip6->ip6_src;
		}

		// Linux seems to not honor IPV6_PKTINFO on raw-sockets, so work around
		setsockopt(ping_socket, SOL_SOCKET, SO_BINDTODEVICE, iface->ifname, sizeof(iface->ifname));
		struct iovec iov = { &advert, sizeof(advert) };
		relayd_forward_packet(ping_socket, &dest, &iov, 1, iface);
	} else {
		// Send echo to all other interfaces to see where target is on
		// This will trigger neighbor discovery which is what we want.
		// We will observe the neighbor cache to see results.

		ssize_t sent = 0;
		if(iface != &config->master) {
			sent += ping6(&req->nd_ns_target, &config->master);
		}

		for(size_t i = 0; i < config->slavecount; ++i) {
			if((!ns_is_dad || config->slaves[i].external == false) && iface != &config->slaves[i]) {
				sent += ping6(&req->nd_ns_target, &config->slaves[i]);
			}
		}

		if(sent > 0) { // Sent a ping, add pending neighbor entry
			modify_neighbor(&req->nd_ns_target, NULL, true);
		}
	}
}

void relayd_setup_route(const struct in6_addr *addr, int prefixlen, const struct relayd_interface *iface, const struct in6_addr *gw, bool add) {
	struct nl_route {
		struct nlmsghdr nlmh;
		struct rtmsg rtm;
		char rta[RTA_SPACE(sizeof(struct in6_addr)) + RTA_SPACE(sizeof(iface->ifindex)) + RTA_SPACE(sizeof(struct in6_addr))];
	} nl_route = { 0 };

	// NLMSGHDR: Netlink message header
	nl_route.nlmh.nlmsg_len = NLMSG_LENGTH(sizeof(struct rtmsg));
	nl_route.nlmh.nlmsg_seq = ++rtnl_seqid;

	// RTMSG: Route message
	nl_route.rtm.rtm_family = AF_INET6;
	nl_route.rtm.rtm_dst_len = prefixlen;
	nl_route.rtm.rtm_table = RT_TABLE_MAIN;
	nl_route.rtm.rtm_protocol = RTPROT_6RELAYD;

	if(add) {
		nl_route.nlmh.nlmsg_type = RTM_NEWROUTE;
		nl_route.nlmh.nlmsg_flags = NLM_F_REQUEST | NLM_F_CREATE | NLM_F_REPLACE;
		nl_route.rtm.rtm_scope = (gw) ? RT_SCOPE_UNIVERSE : RT_SCOPE_LINK;
		nl_route.rtm.rtm_type = RTN_UNICAST;
	} else {
		nl_route.nlmh.nlmsg_type = RTM_DELROUTE;
		nl_route.nlmh.nlmsg_flags = NLM_F_REQUEST;
		nl_route.rtm.rtm_scope = RT_SCOPE_NOWHERE;
	}

	// RTATTR
	int *rta_pos = &(nl_route.nlmh.nlmsg_len);

	// RTA_DST: Route destination address
	struct rtattr *rta_dst = (struct rtattr *) (((char *) &nl_route) + NLMSG_ALIGN(*rta_pos));
	rta_dst->rta_type = RTA_DST;
	rta_dst->rta_len = RTA_LENGTH(sizeof(struct in6_addr));
	memcpy(RTA_DATA(rta_dst), addr, sizeof(struct in6_addr));
	*rta_pos = NLMSG_ALIGN(*rta_pos) + RTA_LENGTH(sizeof(struct in6_addr));

	// RTA_OIF: Output interface index
	struct rtattr *rta_oif = (struct rtattr *) (((char *) &nl_route) + NLMSG_ALIGN(*rta_pos));
	rta_oif->rta_type = RTA_OIF;
	rta_oif->rta_len = RTA_LENGTH(sizeof(iface->ifindex));
	memcpy(RTA_DATA(rta_oif), &iface->ifindex, sizeof(iface->ifindex));
	*rta_pos = NLMSG_ALIGN(*rta_pos) + RTA_LENGTH(sizeof(iface->ifindex));

	if(gw) {
		// RTA_GATEWAY: The gateway of the route
		struct rtattr *rta_gw = (struct rtattr *) (((char *) &nl_route) + NLMSG_ALIGN(*rta_pos));
		rta_gw->rta_type = RTA_GATEWAY;
		rta_gw->rta_len = RTA_LENGTH(sizeof(struct in6_addr));
		memcpy(RTA_DATA(rta_gw), gw, sizeof(struct in6_addr));
		*rta_pos = NLMSG_ALIGN(*rta_pos) + RTA_LENGTH(sizeof(struct in6_addr));
	}

	send(rtnl_event.socket, &nl_route, *rta_pos, MSG_DONTWAIT);
}

static void setup_route(struct in6_addr *addr, struct relayd_interface *iface, bool add) {
	char namebuf[INET6_ADDRSTRLEN];
	inet_ntop(AF_INET6, addr, namebuf, sizeof(namebuf));
	syslog(LOG_NOTICE, "%s about %s on %s", (add) ? "Learned" : "Forgot", namebuf, (iface) ? iface->ifname : "<pending>");

	if(!iface || !config->enable_route_learning) {
		return;
	}

	static const const char *ADD = "Add";
	static const const char *DEL = "Delete";
	printf("I: %s route: %s -> %s\n", add ? ADD : DEL, namebuf, iface->ifname);

	relayd_setup_route(addr, 128, iface, NULL, add);
}

static void free_neighbor(struct ndp_neighbor *n) {
	setup_route(&n->addr, n->iface, false);
	list_del(&n->head);
	free(n);
	--neighbor_count;
}

static bool match_neighbor(struct ndp_neighbor *n, struct in6_addr *addr) {
	if(n->len <= 32) {
		return ntohl(n->addr.s6_addr32[0]) >> (32 - n->len) == ntohl(addr->s6_addr32[0]) >> (32 - n->len);
	}

	if(n->addr.s6_addr32[0] != addr->s6_addr32[0]) {
		return false;
	}

	if(n->len <= 64) {
		return ntohl(n->addr.s6_addr32[1]) >> (64 - n->len) == ntohl(addr->s6_addr32[1]) >> (64 - n->len);
	}

	if(n->addr.s6_addr32[1] != addr->s6_addr32[1]) {
		return false;
	}

	if(n->len <= 96) {
		return ntohl(n->addr.s6_addr32[2]) >> (96 - n->len) == ntohl(addr->s6_addr32[2]) >> (96 - n->len);
	}

	if(n->addr.s6_addr32[2] != addr->s6_addr32[2]) {
		return false;
	}

	return ntohl(n->addr.s6_addr32[3]) >> (128 - n->len) == ntohl(addr->s6_addr32[3]) >> (128 - n->len);
}

static struct ndp_neighbor *find_neighbor(struct in6_addr *addr, bool strict) {
	time_t now = time(NULL);
	struct ndp_neighbor *n, *e;
	list_for_each_entry_safe(n, e, &neighbors, head) {
		if((!strict && match_neighbor(n, addr)) || (n->len == 128 && IN6_ARE_ADDR_EQUAL(&n->addr, addr))) {
			return n;
		}

		if(!n->iface && abs(n->timeout - now) >= 5) {
			free_neighbor(n);
		}
	}
	return NULL;
}

// Modified our own neighbor-entries
static void modify_neighbor(struct in6_addr *addr, struct relayd_interface *iface, bool add) {
	if(!addr || (void *) addr == (void *) iface) {
		return;
	}

	struct ndp_neighbor *n = find_neighbor(addr, true);
	if(!add) { // Delete action
		if(n && (!n->iface || n->iface == iface)) {
			free_neighbor(n);
		}
	} else if(!n) { // No entry yet, add one if possible
		if(neighbor_count >= NDP_MAX_NEIGHBORS || !(n = malloc(sizeof(*n)))) {
			return;
		}

		n->len = 128;
		n->addr = *addr;
		n->iface = iface;
		if(!n->iface) {
			time(&n->timeout);
		}
		list_add(&n->head, &neighbors);
		++neighbor_count;
		setup_route(addr, n->iface, add);
	} else if(n->iface == iface) {
		if(!n->iface) {
			time(&n->timeout);
		}
	} else if(iface && (!n->iface || (!iface->external && n->iface->external))) {
		setup_route(addr, n->iface, false);
		n->iface = iface;
		setup_route(addr, n->iface, add);
	}
	// TODO: In case a host switches interfaces we might want
	// to set its old neighbor entry to NUD_STALE and ping it
	// on the old interface to confirm if the MACs match.
}

// Handler for neighbor cache entries from the kernel. This is our source
// to learn and unlearn hosts on interfaces.
static void handle_rtnetlink(_unused void *addr, void *data, size_t len, _unused struct relayd_interface *iface) {
	for(struct nlmsghdr *nh = data; NLMSG_OK(nh, len); nh = NLMSG_NEXT(nh, len)) {
		struct rtmsg *rtm = NLMSG_DATA(nh);
		if(config->enable_router_discovery_server && (nh->nlmsg_type == RTM_NEWROUTE || nh->nlmsg_type == RTM_DELROUTE) && rtm->rtm_dst_len == 0) {
			raise(SIGUSR1); // Inform about a change in default route
		}

		struct ndmsg *ndm = NLMSG_DATA(nh);
		struct ifaddrmsg *ifa = NLMSG_DATA(nh);
		if(nh->nlmsg_type != RTM_NEWNEIGH && nh->nlmsg_type != RTM_DELNEIGH && nh->nlmsg_type != RTM_NEWADDR && nh->nlmsg_type != RTM_DELADDR) {
			continue; // Unrelated message type
		}
		bool is_addr = (nh->nlmsg_type == RTM_NEWADDR || nh->nlmsg_type == RTM_DELADDR);

		// Family and ifindex are on the same offset for NEIGH and ADDR
		if(NLMSG_PAYLOAD(nh, 0) < sizeof(*ndm) || ndm->ndm_family != AF_INET6) {
			continue; //
		}

		// Lookup interface
		struct relayd_interface *iface;
		if(!(iface = relayd_get_interface_by_index(ndm->ndm_ifindex))) {
			continue;
		}

		// Data to retrieve
		size_t rta_offset = (is_addr) ? sizeof(*ifa) : sizeof(*ndm);
		uint16_t atype = (is_addr) ? IFA_ADDRESS : NDA_DST;
		ssize_t alen = NLMSG_PAYLOAD(nh, rta_offset);
		struct in6_addr *addr = NULL;

		for(struct rtattr *rta = (void *) (((uint8_t *) ndm) + rta_offset); RTA_OK(rta, alen); rta = RTA_NEXT(rta, alen)) {
			if(rta->rta_type == atype && RTA_PAYLOAD(rta) >= sizeof(*addr)) {
				addr = RTA_DATA(rta);
			}
		}

		// Address not specified or unrelated
		if(!addr || IN6_IS_ADDR_LINKLOCAL(addr) || IN6_IS_ADDR_MULTICAST(addr)) {
			continue;
		}

		// Check for states
		bool add;
		if(is_addr) {
			add = (nh->nlmsg_type == RTM_NEWADDR);
		} else {
			add = (nh->nlmsg_type == RTM_NEWNEIGH && (ndm->ndm_state & (NUD_REACHABLE | NUD_STALE | NUD_DELAY | NUD_PROBE | NUD_PERMANENT | NUD_NOARP)));
		}

		if(config->enable_ndp_relay) {
			modify_neighbor(addr, iface, add);
		}

		if(is_addr && config->enable_router_discovery_server) {
			raise(SIGUSR1); // Inform about a change in addresses
		}

		if(is_addr && config->enable_dhcpv6_server) {
			iface->pd_reconf = true;
		}

		if(config->enable_ndp_relay && is_addr && iface == &config->master) {
			// Replay address changes on all slave interfaces
			nh->nlmsg_flags = NLM_F_REQUEST;

			if(nh->nlmsg_type == RTM_NEWADDR) {
				nh->nlmsg_flags |= NLM_F_CREATE | NLM_F_REPLACE;
			}

			for(size_t i = 0; i < config->slavecount; ++i) {
				ifa->ifa_index = config->slaves[i].ifindex;
				send(rtnl_event.socket, nh, nh->nlmsg_len, MSG_DONTWAIT);
			}
		}

		/* TODO: See if this is required for optimal operation
    // Keep neighbor entries alive so we don't loose routes
    if (add && (ndm->ndm_state & NUD_STALE))
            ping6(addr, iface);
    */
	}
}
