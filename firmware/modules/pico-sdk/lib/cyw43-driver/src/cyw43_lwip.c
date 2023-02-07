/*
 * This file is part of the cyw43-driver
 *
 * Copyright (C) 2019-2022 George Robotics Pty Ltd
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 * 3. Any redistribution, use, or modification in source or binary form is done
 *    solely for personal benefit and not for any commercial purpose or for
 *    monetary gain.
 *
 * THIS SOFTWARE IS PROVIDED BY THE LICENSOR AND COPYRIGHT OWNER "AS IS" AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE LICENSOR OR COPYRIGHT OWNER BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * This software is also available for use with certain devices under different
 * terms, as set out in the top level LICENSE file.  For commercial licensing
 * options please email contact@georgerobotics.com.au.
 */

#include <stdio.h>
#include <string.h>

#include "cyw43.h"
#include "cyw43_stats.h"
#if CYW43_LWIP
#include "lwip/etharp.h"
#include "lwip/dns.h"
#include "lwip/apps/mdns.h"
#include "lwip/tcpip.h"
#include "netif/ethernet.h"
#endif

#if CYW43_NETUTILS
#include "shared/netutils/netutils.h"
#endif

#if CYW43_LWIP

#if CYW43_NETUTILS
STATIC void cyw43_ethernet_trace(cyw43_t *self, struct netif *netif, size_t len, const void *data, unsigned int flags) {
    bool is_tx = flags & NETUTILS_TRACE_IS_TX;
    if ((is_tx && (self->trace_flags & CYW43_TRACE_ETH_TX))
        || (!is_tx && (self->trace_flags & CYW43_TRACE_ETH_RX))) {
        const uint8_t *buf;
        if (len == (size_t)-1) {
            // data is a pbuf
            const struct pbuf *pbuf = data;
            buf = pbuf->payload;
            len = pbuf->len; // restricted to print only the first chunk of the pbuf
        } else {
            // data is actual data buffer
            buf = data;
        }

        if (self->trace_flags & CYW43_TRACE_MAC) {
            CYW43_PRINTF("[% 8d] ETH%cX itf=%c%c len=%u", (int)cyw43_hal_ticks_ms(), is_tx ? 'T' : 'R', netif->name[0], netif->name[1], len);
            CYW43_PRINTF(" MAC type=%d subtype=%d data=", buf[0] >> 2 & 3, buf[0] >> 4);
            for (size_t i = 0; i < len; ++i) {
                CYW43_PRINTF(" %02x", buf[i]);
            }
            CYW43_PRINTF("\n");
            return;
        }

        if (self->trace_flags & CYW43_TRACE_ETH_FULL) {
            flags |= NETUTILS_TRACE_PAYLOAD;
        }
        netutils_ethernet_trace(MP_PYTHON_PRINTER, len, buf, flags);
    }
}
#endif

STATIC err_t cyw43_netif_output(struct netif *netif, struct pbuf *p) {
    cyw43_t *self = netif->state;
    #if CYW43_NETUTILS
    if (self->trace_flags != 0) {
        cyw43_ethernet_trace(self, netif, (size_t)-1, p, NETUTILS_TRACE_IS_TX | NETUTILS_TRACE_NEWLINE);
    }
    #endif
    int itf = netif->name[1] - '0';
    int ret = cyw43_send_ethernet(self, itf, p->tot_len, (void *)p, true);
    if (ret) {
        CYW43_WARN("send_ethernet failed: %d\n", ret);
        return ERR_IF;
    }
    CYW43_STAT_INC(PACKET_OUT_COUNT);
    return ERR_OK;
}

STATIC err_t cyw43_netif_init(struct netif *netif) {
    netif->linkoutput = cyw43_netif_output;
    netif->output = etharp_output;
    netif->mtu = 1500;
    netif->flags = NETIF_FLAG_BROADCAST | NETIF_FLAG_ETHARP | NETIF_FLAG_ETHERNET | NETIF_FLAG_IGMP;
    cyw43_wifi_get_mac(netif->state, netif->name[1] - '0', netif->hwaddr);
    netif->hwaddr_len = sizeof(netif->hwaddr);
    return ERR_OK;
}

//#ifndef NDEBUG
//static void netif_status_callback(struct netif *netif) {
//    const ip_addr_t *ip = netif_ip_addr4(netif);
//    if (ip) {
//        CYW43_INFO("Got ip %s\n", ip4addr_ntoa(ip));
//    }
//}
//#endif

#ifndef CYW43_HOST_NAME
#define CYW43_HOST_NAME "PYBD"
#endif

void cyw43_cb_tcpip_init(cyw43_t *self, int itf) {
    ip_addr_t ipconfig[4];
    #if LWIP_IPV6
    #define IP(x) ((x).u_addr.ip4)
    #else
    #define IP(x) (x)
    #endif
    if (itf == 0) {
        // need to zero out to get isconnected() working
        IP4_ADDR(&IP(ipconfig[0]), 0, 0, 0, 0);
        IP4_ADDR(&IP(ipconfig[2]), 192, 168, 0, 1);
    } else {
        IP4_ADDR(&IP(ipconfig[0]), 192, 168, 4, 1);
        IP4_ADDR(&IP(ipconfig[2]), 192, 168, 4, 1);
    }
    IP4_ADDR(&IP(ipconfig[1]), 255, 255, 255, 0);
    IP4_ADDR(&IP(ipconfig[3]), 8, 8, 8, 8);
    #undef IP

    struct netif *n = &self->netif[itf];
    n->name[0] = 'w';
    n->name[1] = '0' + itf;
    #if NO_SYS
    #if LWIP_IPV6
    netif_add(n, &ipconfig[0].u_addr.ip4, &ipconfig[1].u_addr.ip4, &ipconfig[2].u_addr.ip4, self, cyw43_netif_init, ethernet_input);
    #else
    netif_add(n, &ipconfig[0], &ipconfig[1], &ipconfig[2], self, cyw43_netif_init, ethernet_input);
    #endif
    #else
    netif_add(n, &ipconfig[0], &ipconfig[1], &ipconfig[2], self, cyw43_netif_init, tcpip_input);
    #endif
    netif_set_hostname(n, CYW43_HOST_NAME);
    netif_set_default(n);
    netif_set_up(n);

//    #ifndef NDEBUG
//    netif_set_status_callback(n, netif_status_callback);
//    #endif

    if (itf == CYW43_ITF_STA) {
        dns_setserver(0, &ipconfig[3]);
        dhcp_set_struct(n, &self->dhcp_client);
        dhcp_start(n);
    } else {
        #if CYW43_NETUTILS
        dhcp_server_init(&self->dhcp_server, &ipconfig[0], &ipconfig[1]);
        #endif
    }

    #if LWIP_MDNS_RESPONDER
    // TODO better to call after IP address is set
    char mdns_hostname[9];
    memcpy(&mdns_hostname[0], CYW43_HOST_NAME, 4);
    cyw43_hal_get_mac_ascii(CYW43_HAL_MAC_WLAN0, 8, 4, &mdns_hostname[4]);
    mdns_hostname[8] = '\0';
    mdns_resp_add_netif(n, mdns_hostname, 60);
    #endif
}

void cyw43_cb_tcpip_deinit(cyw43_t *self, int itf) {
    struct netif *n = &self->netif[itf];
    if (itf == CYW43_ITF_STA) {
        dhcp_stop(n);
    } else {
        #if CYW43_NETUTILS
        dhcp_server_deinit(&self->dhcp_server);
        #endif
    }
    #if LWIP_MDNS_RESPONDER
    mdns_resp_remove_netif(n);
    #endif
    for (struct netif *netif = netif_list; netif != NULL; netif = netif->next) {
        if (netif == n) {
            netif_remove(netif);
            netif->ip_addr.addr = 0;
            netif->flags = 0;
        }
    }
}

void cyw43_cb_process_ethernet(void *cb_data, int itf, size_t len, const uint8_t *buf) {
    cyw43_t *self = cb_data;
    struct netif *netif = &self->netif[itf];
    #if CYW43_NETUTILS
    if (self->trace_flags) {
        cyw43_ethernet_trace(self, netif, len, buf, NETUTILS_TRACE_NEWLINE);
    }
    #endif
    if (netif->flags & NETIF_FLAG_LINK_UP) {
        struct pbuf *p = pbuf_alloc(PBUF_RAW, len, PBUF_POOL);
        if (p != NULL) {
            pbuf_take(p, buf, len);
            if (netif->input(p, netif) != ERR_OK) {
                pbuf_free(p);
            }
            CYW43_STAT_INC(PACKET_IN_COUNT);
        }
    }
}

void cyw43_cb_tcpip_set_link_up(cyw43_t *self, int itf) {
    netif_set_link_up(&self->netif[itf]);
}

void cyw43_cb_tcpip_set_link_down(cyw43_t *self, int itf) {
    netif_set_link_down(&self->netif[itf]);
}

int cyw43_tcpip_link_status(cyw43_t *self, int itf) {
    struct netif *netif = &self->netif[itf];
    if ((netif->flags & (NETIF_FLAG_UP | NETIF_FLAG_LINK_UP))
        == (NETIF_FLAG_UP | NETIF_FLAG_LINK_UP)) {
        if (netif->ip_addr.addr != 0) {
            return CYW43_LINK_UP;
        } else {
            return CYW43_LINK_NOIP;
        }
    } else {
        return cyw43_wifi_link_status(self, itf);
    }
}

#endif //  CYW43_LWIP
