#pragma once

#include <stdint.h>
#include <string.h>

/**
 * Ring of the newest fixed-size messages with one read position per client. A client that falls behind skips the
 * oldest messages, so memory use is fixed and a slow client never holds up the others. Not thread safe.
 */
template <uint16_t kMessageNumBytes, uint16_t kDepth, uint16_t kMaxNumClients>
class BroadcastRing {
    static_assert((kDepth & (kDepth - 1)) == 0, "kDepth must be a power of two.");

   public:
    void Push(const uint8_t* message) {
        memcpy(messages_[num_pushed_ % kDepth], message, kMessageNumBytes);
        num_pushed_++;
    }

    /**
     * Sets the connected clients. New clients start at the next pushed message; clients missing from the list are
     * forgotten.
     * @param[in] client_ids IDs of the connected clients. Must be >= 0.
     * @param[in] num_clients Number of IDs. IDs past kMaxNumClients are ignored.
     */
    void SetClients(const int* client_ids, uint16_t num_clients) {
        for (uint16_t i = 0; i < kMaxNumClients; i++) {
            bool connected = false;
            for (uint16_t j = 0; j < num_clients && !connected; j++) {
                connected = clients_[i].id == client_ids[j];
            }
            if (!connected) clients_[i].id = kNoClient;
        }
        for (uint16_t j = 0; j < num_clients; j++) {
            if (FindClient(client_ids[j])) continue;
            Client* free_client = FindClient(kNoClient);
            if (!free_client) return;
            free_client->id = client_ids[j];
            free_client->num_read = num_pushed_;
        }
    }

    /**
     * Next unread message for a client. Skips messages that were overwritten and counts them in num_dropped.
     * @retval Pointer to the message, valid until the next Push(), or nullptr if the client is up to date or unknown.
     */
    const uint8_t* Peek(int client_id) {
        Client* client = FindClient(client_id);
        if (!client || client->num_read == num_pushed_) return nullptr;
        uint32_t num_unread = num_pushed_ - client->num_read;
        if (num_unread > kDepth) {
            num_dropped += num_unread - kDepth;
            client->num_read = num_pushed_ - kDepth;
        }
        return messages_[client->num_read % kDepth];
    }

    // Marks the message returned by Peek() as read.
    void Pop(int client_id) {
        Client* client = FindClient(client_id);
        if (client && client->num_read != num_pushed_) client->num_read++;
    }

    uint32_t num_dropped = 0;  // Messages skipped by slow clients, summed over clients.

   private:
    static constexpr int kNoClient = -1;
    struct Client {
        int id = kNoClient;
        uint32_t num_read = 0;  // Value of num_pushed_ at the client's read position.
    };

    Client* FindClient(int client_id) {
        for (uint16_t i = 0; i < kMaxNumClients; i++) {
            if (clients_[i].id == client_id) return &clients_[i];
        }
        return nullptr;
    }

    uint8_t messages_[kDepth][kMessageNumBytes];
    Client clients_[kMaxNumClients];
    uint32_t num_pushed_ = 0;
};
