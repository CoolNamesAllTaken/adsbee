#include "at_command_parser.hh"

#include "string.h"
#include <sstream> // stringstream for splitting using getline()

/**
 * Initialize static const member variables.
*/
const std::string ATCommandParser::kATPrefix = "AT";
const size_t ATCommandParser::kATPrefixLen = kATPrefix.length();

/**
 * Public Functions
*/

/**
 * @brief Constructor.
 * @param[in] at_command_list_in std::vector of ATCommandDef_t's that define what AT commands are supported
 * as well as their corresponding callback functions.
*/
ATCommandParser::ATCommandParser(std::vector<ATCommandDef_t> at_command_list_in)
    : at_command_list(at_command_list_in)
{

}

/**
 * @brief Destructor. Deallocates dynamically allocated memory.
*/
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

/**
 * @brief Returns a pointer to the first ATCommandDef_t object that matches the text command provided.
 * @param[in] command String containing command text to look for.
 * @retval Pointer to corresponding ATCommandDef_t within the at_command_list, or nullptr if not found.
*/
ATCommandParser::ATCommandDef_t * ATCommandParser::LookupATCommand(std::string command) {
    if (command.length() > kATCommandMaxLen) {
        return nullptr; // Command is too long, not supported.
    }
    for (ATCommandDef_t& def: at_command_list) {
        if (command.compare(0, kATCommandMaxLen, def.command) == 0) {
            return &def;
        }
    }
    return nullptr;
}

/**
 * @brief Parses a message to find the AT command, match it with the relevant ATCommandDef_t, parse
 * out the arguments and execute the corresponding callback function.
*/
bool ATCommandParser::ParseMessage(std::string message) {
    // Message should start with "AT"
    std::size_t start = message.find(kATPrefix);
    if (start == std::string::npos) {
        printf("ATCommandParser::ParseMessage: Unable to find AT prefix in string %s.\r\n", message.c_str());
        return false;
    }

    while (start != std::string::npos) {
        start += kATPrefixLen; // Start after the AT prefix.

        // Command is everything between AT prefix and the first comma, space, equal sign, or newline.
        size_t command_end = message.find_first_of(", =\n", start);
        std::string command = message.substr(start, command_end == std::string::npos ? std::string::npos : command_end - start);
        if (command.length() == 0) {
            printf("ATCommandParser::ParseMessage: Can't parse 0 length command in string %s.\r\n", message.c_str());
            return false;
        }
        // Try matching the command text with an AT command definition.
        ATCommandDef_t * def = LookupATCommand(command);
        if (def == nullptr) {
            printf("ATCommandParser::ParseMessage: Unable to match AT command %s.\r\n", command.c_str());
            return false;
        }
        

        // Parse out the arguments
        start+=command.length()+1; // Shift start to beginning of args (end of command+delimiter).
        // Args are everything between command and newline.
        std::stringstream args_string(message.substr(start, message.find_first_of("\n", start)));
        std::string arg;
        std::vector<std::string> args_list;
        while(std::getline(args_string, arg, ',')) {
            args_list.push_back(arg);
        }
        if (def->callback) {
            bool result = def->callback(args_list);
            if (!result) {
                printf("ATCommandParser::ParseMessage: Call to AT Command %s with args %s failed.\r\n", command.c_str(), args_string.str().c_str());
                return false;
            }
        } else {
            printf("ATCommandParser::ParseMessage: Received a call to AT command %s with no corresponding callback function.\r\n", command.c_str());
        }

        // Look for the next AT command. Skip to next AT prefix after the newline.
        start = message.find(kATPrefix, start);
    }

    return true;
}

/**
 * Private Functions
*/