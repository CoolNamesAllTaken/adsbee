// #ifndef IP_UTILS_HH_
// #define IP_UTILS_HH_

// #include <lwip/netdb.h>
// #include <stdio.h>
// #include <string.h>

// #include "esp_log.h"
// #include "lwip/err.h"
// #include "lwip/sockets.h"
// #include "lwip/sys.h"

// static const uint16_t kIPStrBufLenChars = 20;

// /**
//  * @brief Get the destination IP address of a socket
//  * @param[in] sock The socket file descriptor
//  * @param[out] buffer Buffer to store the IP address string
//  * @param[in] port Pointer to store the port number (can be NULL if not needed)
//  * @return esp_err_t ESP_OK on success, ESP_FAIL on failure
//  */
// esp_err_t SocketToIPStr(int sock, char* buffer, uint16_t* port) {
//     struct sockaddr_in peer_addr;
//     socklen_t peer_addr_len = sizeof(peer_addr);

//     // Get the peer address information
//     if (getpeername(sock, (struct sockaddr*)&peer_addr, &peer_addr_len) != 0) {
//         buffer[0] = '\0';  // Ensure buffer is null-terminated
//         return ESP_FAIL;
//     }

//     // Convert IP address to string
//     if (inet_ntop(AF_INET, &peer_addr.sin_addr, buffer, kIPStrBufLenChars) == NULL) {
//         buffer[0] = '\0';  // Ensure buffer is null-terminated
//         return ESP_FAIL;
//     }

//     // Store port if requested
//     if (port != NULL) {
//         *port = ntohs(peer_addr.sin_port);
//     }

//     return ESP_OK;
// }

// #endif