#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>

// Streaming JSON reader for small devices: feed it the text in pieces of any size and it reports scalar values and
// container boundaries. It keeps one token in memory, never the document. Values longer than kTokenMaxLen are cut.
class JsonScanner {
   public:
    static constexpr size_t kTokenMaxLen = 199;
    static constexpr size_t kKeyMaxLen = 31;
    static constexpr uint8_t kMaxDepth = 16;

    class Handler {
       public:
        virtual ~Handler() {}
        // A string, number, true, false or null. depth is the nesting level of its container (1 = top level).
        virtual void OnValue(const char* key, const char* value, bool is_string, uint8_t depth) = 0;
        // '{' or '[' opened under key. depth is the new container's level.
        virtual void OnOpen(char bracket, const char* key, uint8_t depth) {}
        // The container at depth closed.
        virtual void OnClose(char bracket, uint8_t depth) {}
    };

    explicit JsonScanner(Handler& handler) : handler_(handler) {}

    void Feed(const char* data, size_t len) {
        for (size_t i = 0; i < len; i++) Push(data[i]);
    }

    // False after malformed nesting.
    bool ok() const { return ok_; }
    // True once the top-level value has closed.
    bool complete() const { return ok_ && started_ && depth_ == 0; }

   private:
    void Push(char c) {
        if (in_string_) {
            if (escape_) {
                escape_ = false;
                Append(c == 'n' ? '\n' : c == 't' ? '\t' : c == 'u' ? '?' : c);
            } else if (c == '\\') {
                escape_ = true;
            } else if (c == '"') {
                in_string_ = false;
                have_string_ = true;
            } else {
                Append(c);
            }
            return;
        }
        switch (c) {
            case '"':
                in_string_ = true;
                tok_len_ = 0;
                break;
            case ':':
                tok_[tok_len_] = '\0';
                strncpy(key_, tok_, kKeyMaxLen);
                key_[kKeyMaxLen] = '\0';
                have_string_ = false;
                tok_len_ = 0;
                break;
            case '{':
            case '[':
                started_ = true;
                if (depth_ >= kMaxDepth) {
                    ok_ = false;
                    break;
                }
                depth_++;
                handler_.OnOpen(c, key_, depth_);
                key_[0] = '\0';
                tok_len_ = 0;
                break;
            case '}':
            case ']':
                Flush();
                if (depth_ == 0) {
                    ok_ = false;
                    break;
                }
                handler_.OnClose(c, depth_);
                depth_--;
                break;
            case ',':
                Flush();
                break;
            case ' ':
            case '\t':
            case '\r':
            case '\n':
                break;
            default:
                Append(c);  // Part of a number, true, false or null.
                break;
        }
    }

    void Append(char c) {
        if (tok_len_ < kTokenMaxLen) tok_[tok_len_++] = c;
    }

    void Flush() {
        if (have_string_ || tok_len_ > 0) {
            tok_[tok_len_] = '\0';
            handler_.OnValue(key_, tok_, have_string_, depth_);
        }
        have_string_ = false;
        tok_len_ = 0;
        key_[0] = '\0';
    }

    Handler& handler_;
    char tok_[kTokenMaxLen + 1] = {0};
    size_t tok_len_ = 0;
    char key_[kKeyMaxLen + 1] = {0};
    uint8_t depth_ = 0;
    bool in_string_ = false;
    bool escape_ = false;
    bool have_string_ = false;
    bool started_ = false;
    bool ok_ = true;
};
