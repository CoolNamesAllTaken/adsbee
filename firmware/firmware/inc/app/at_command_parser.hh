#ifndef _AT_COMMAND_PARSER_HH_
#define _AT_COMMAND_PARSER_HH_

#include "stdint.h"
#include <string>
#include <functional>
#include <vector>

class ATCommandParser {
public:
    static const uint16_t kATCommandMaxLen = 16;
    // Initialized in .cc file.
    static const char kATPrefix[];
    static const uint16_t kATPrefixLen;
    static const char kATAllowedOpChars[];
    static const uint16_t kHelpStringMaxLen = 100;

    struct ATCommandDef_t {
        std::string command = ""; // Letters that come after the "AT+" prefix.
        uint16_t min_args = 0; // Minimum number of arguments to expect after AT+<command>.
        uint16_t max_args = 100; // Maximum number of arguments to expect after AT+<command>.
        char help_string[kHelpStringMaxLen] = "Help string not defined."; // Text to print when listing available AT commands.
        std::function<bool(char,std::vector<std::string>)> callback = nullptr; // FUnction to call with list of arguments.
    };

    ATCommandParser(); // default constructor
    ATCommandParser(const ATCommandDef_t * at_command_list_in); // Constructor.
    ~ATCommandParser(); // Destructor.

    void SetATCommandList(const ATCommandDef_t * at_command_list_in);
    uint16_t GetNumATCommands();
    ATCommandDef_t * LookupATCommand(std::string command);
    bool ParseMessage(std::string message);

private:
    ATCommandDef_t * at_command_list_;

    bool ATHelpCallback(char op, std::vector<std::string> args);
};


#endif