#ifndef _AT_COMMAND_PARSER_HH_
#define _AT_COMMAND_PARSER_HH_

#include "stdint.h"
#include <string_view>
#include <functional>
#include <vector>

class ATCommandParser {
public:
    static const uint16_t kATCommandMaxLen = 16;
    // Initialized in .cc file.
    static const char kATPrefix[];
    static const uint16_t kATPrefixLen;
    static const char kATAllowedOpChars[];
    static const uint16_t kHelpStringMaxLen = 500;
    static const char kArgDelimiter = ',';
    static const char kATMessageEndStr[];

    struct ATCommandDef_t {
        char command_buf[kATCommandMaxLen] = "";
        std::string_view command = {command_buf}; // Letters that come after the "AT+" prefix.
        uint16_t min_args = 0; // Minimum number of arguments to expect after AT+<command>.
        uint16_t max_args = 100; // Maximum number of arguments to expect after AT+<command>.
        char help_string_buf[kHelpStringMaxLen] = "Help string not defined."; // Text to print when listing available AT commands.
        std::string_view help_string = {help_string_buf};
        std::function<bool(char,std::vector<std::string_view>)> callback = nullptr; // FUnction to call with list of arguments.
    };

    ATCommandParser(); // default constructor
    ATCommandParser(const ATCommandDef_t * at_command_list_in); // Constructor.
    ~ATCommandParser(); // Destructor.

    void SetATCommandList(const ATCommandDef_t * at_command_list_in);
    uint16_t GetNumATCommands();
    ATCommandDef_t * LookupATCommand(std::string_view command);
    bool ParseMessage(std::string_view message);

    // Helper functions for callbacks.
    static inline bool ArgToNum(std::string_view arg, auto &number, uint16_t base=10);

private:
    ATCommandDef_t * at_command_list_;
    uint16_t num_at_commands_;

    bool ATHelpCallback(char op, std::vector<std::string_view> args);
};


#endif