#include "at_command_parser.hh"

#include "string.h"

/**
 * Public Functions
*/

ATCommandParser::ATCommandParser(std::vector<ATCommandDef_t> at_command_list_in)
    : at_command_list(at_command_list_in)
{
    // for (ATCommandDef_t * command: at_command_list_in) {
    //     // Copy AT command definitions 
    //     at_command_list.push_back(command);
    // }

}

ATCommandParser::~ATCommandParser() {
    at_command_list.clear(); // Note: this works as long as elements are objects and not pointers.
}

/**
 * @brief Returns the number of supported AT commands.
 * @retval Size of at_command_list.
*/
uint16_t ATCommandParser::GetNumATCommands() {
    return at_command_list.size();
}

bool ATCommandParser::ParseMessage(std::string message) {
    // Message should start with "AT+"
    std::size_t start = message.find("AT+");
    if (start == std::string::npos) {
        printf("ATCommandParser::ParseMessage: Unable to find AT+ prefix in string %s", message);
        return false;
    }

    return true;
}

/**
 * Private Functions
*/

/**
 * @brief Returns a pointer to the first ATCommandDef_t object that matches the text command provided.
 * @param[in] command String containing command text to look for.
 * @retval Pointer to corresponding ATCommandDef_t within the at_command_list, or nullptr if not found.
*/
ATCommandParser::ATCommandDef_t * ATCommandParser::LookupATCommand(std::string command) {
    for (ATCommandDef_t& def: at_command_list) {
        if (command.compare(0, kATCommandMaxLen, def.command) == 0) {
            return &def;
        }
    }
    return nullptr;
}