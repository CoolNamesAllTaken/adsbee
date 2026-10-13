#pragma once

#include <cstdint>

/**
 * Remembers when each open HTTP session was last used, so that sessions a client keeps open without using them can be
 * closed. Not thread safe.
 */
template <uint16_t kMaxNumSessions>
class IdleSessionTracker {
   public:
    /**
     * Starts tracking a session. A session already tracked under this file descriptor is replaced.
     * @retval False if kMaxNumSessions other sessions are tracked.
     */
    bool Open(int fd, uint32_t timestamp_ms) {
        Session* session = Find(fd);
        if (session == nullptr) {
            session = Find(kUnusedFd);
        }
        if (session == nullptr || fd < 0) {
            return false;
        }
        session->fd = fd;
        session->last_used_timestamp_ms = timestamp_ms;
        return true;
    }

    /** Marks a session as used now. */
    void Touch(int fd, uint32_t timestamp_ms) {
        Session* session = fd < 0 ? nullptr : Find(fd);
        if (session != nullptr) {
            session->last_used_timestamp_ms = timestamp_ms;
        }
    }

    void Close(int fd) {
        Session* session = fd < 0 ? nullptr : Find(fd);
        if (session != nullptr) {
            session->fd = kUnusedFd;
        }
    }

    /**
     * @param[in] is_exempt Called with a file descriptor. Sessions it returns true for are never returned.
     * @retval File descriptor of the session unused for the longest time, if that is at least idle_timeout_ms.
     * Otherwise -1.
     */
    template <typename IsExempt>
    int NextIdle(uint32_t timestamp_ms, uint32_t idle_timeout_ms, IsExempt is_exempt) const {
        int idle_fd = -1;
        uint32_t longest_idle_ms = 0;
        for (const Session& session : sessions_) {
            if (session.fd == kUnusedFd) continue;
            uint32_t idle_ms = timestamp_ms - session.last_used_timestamp_ms;  // Correct across timestamp wraps.
            if (idle_ms < idle_timeout_ms || (idle_fd >= 0 && idle_ms <= longest_idle_ms)) continue;
            if (is_exempt(session.fd)) continue;
            idle_fd = session.fd;
            longest_idle_ms = idle_ms;
        }
        return idle_fd;
    }

    int NextIdle(uint32_t timestamp_ms, uint32_t idle_timeout_ms) const {
        return NextIdle(timestamp_ms, idle_timeout_ms, [](int) { return false; });
    }

    uint16_t NumSessions() const {
        uint16_t num_sessions = 0;
        for (const Session& session : sessions_) {
            if (session.fd != kUnusedFd) num_sessions++;
        }
        return num_sessions;
    }

   private:
    static constexpr int kUnusedFd = -1;

    struct Session {
        int fd = kUnusedFd;
        uint32_t last_used_timestamp_ms = 0;
    };

    Session* Find(int fd) {
        for (Session& session : sessions_) {
            if (session.fd == fd) return &session;
        }
        return nullptr;
    }

    Session sessions_[kMaxNumSessions];
};
