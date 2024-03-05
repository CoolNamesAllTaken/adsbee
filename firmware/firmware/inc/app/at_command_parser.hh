#ifndef _AT_COMMAND_PARSER_HH_
#define _AT_COMMAND_PARSER_HH_

#include "stdint.h"
#include <string>
#include <functional>
#include <vector>

class ATCommandParser {
public:
    static const uint16_t kATCommandMaxLen = 16;
    static const std::string kATPrefix; // Initialized in .cc file.
    static const size_t kATPrefixLen; // Initialized in .cc file.

    typedef struct {
        std::string command = ""; // Letters that come after the "AT+" prefix.
        uint16_t min_args = 0; // Minimum number of arguments to expect after AT+<command>.
        uint16_t max_args = 100; // Maximum number of arguments to expect after AT+<command>.
        std::string help_string = "Help string not defined."; // Text to print when listing available AT commands.
        std::function<bool(std::vector<std::string>)> callback = nullptr; // FUnction to call with list of arguments.
    } ATCommandDef_t;

    ATCommandParser(std::vector<ATCommandDef_t> at_command_list_in); // Constructor.
    ~ATCommandParser(); // Destructor.

    uint16_t GetNumATCommands();
    ATCommandDef_t * LookupATCommand(std::string command);
    bool ParseMessage(std::string message);

private:
    std::vector<ATCommandDef_t> at_command_list;

    


};


#endif