#ifndef _AT_COMMAND_PARSER_HH_
#define _AT_COMMAND_PARSER_HH_

#include "stdint.h"
#include <string_view>
#include <functional>
#include <vector>
#include <cctype> // for std::isspace()

class ATCommandParser {
public:
    static const uint16_t kATCommandMaxLen = 16;
    // Initialized in .cc file.
    static const char kATPrefix[];
    static const uint16_t kATPrefixLen;
    static const char kATAllowedOpChars[];
    static const uint16_t kHelpStringMaxLen = 200;
    static const uint16_t kArgMaxLen = 32;
    static const char kArgDelimiter = ',';
    static const uint16_t kMaxNumArgs = 20;
    static const char kATMessageEndStr[];

    struct ATCommandDef_t {
        char command_buf[kATCommandMaxLen+1] = ""; // leave room for '\0'
        std::string_view command = {command_buf}; // Letters that come after the "AT+" prefix.
        uint16_t min_args = 0; // Minimum number of arguments to expect after AT+<command>.
        uint16_t max_args = 100; // Maximum number of arguments to expect after AT+<command>.
        char help_string_buf[kHelpStringMaxLen+1] = "Help string not defined."; // Text to print when listing available AT commands.
        std::string_view help_string = {help_string_buf};
        std::function<bool(char, const std::string_view[], uint16_t)> callback = nullptr; // FUnction to call with list of arguments.
    };

    ATCommandParser(); // default constructor
    ATCommandParser(const ATCommandDef_t * at_command_list_in, uint16_t num_at_commands_in); // Constructor.
    ~ATCommandParser(); // Destructor.

    bool SetATCommandList(const ATCommandDef_t *at_command_list_in, uint16_t num_at_commands_in);
    uint16_t GetNumATCommands();
    ATCommandDef_t * LookupATCommand(std::string_view command);
    bool ParseMessage(std::string_view message);

    bool is_valid = false;

    template<typename T>
    static inline bool ArgToNum(const std::string_view arg, T &number, uint16_t base = 10) {
        char *end_ptr;
        const char *arg_ptr = arg.data();

        // Parse Integer
        int parsed_int = strtol(arg_ptr, &end_ptr, base);
        if (end_ptr != arg_ptr) {
            while (std::isspace(*end_ptr)) ++end_ptr;
            if (*end_ptr == '\0') {
                // NOTE: This may cause unexpected results if type is unsigned but parsed value is signed!
                number = static_cast<T>(parsed_int);
                return true;
            }
            // else: There are numbers or text after the decimal, try parsing float.
        }

        // Parse Float
        float parsed_float = strtof(arg_ptr, &end_ptr);
        if (end_ptr != arg_ptr && *end_ptr == '\0') {
            number = static_cast<T>(parsed_float);
            return true;
        }

        return false; // Failed to parse.
    }

private:
    ATCommandDef_t * at_command_list_;
    uint16_t num_at_commands_;

    bool ATHelpCallback(char op, const std::string_view args[], uint16_t num_args);
};

#endif