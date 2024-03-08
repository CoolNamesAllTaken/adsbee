#include "at_command_parser.hh"

#include "string.h"
#include <sstream> // stringstream for splitting using getline()

/**
 * Initialize static const member variables.
*/
const std::string ATCommandParser::kATPrefix = "AT";
const size_t ATCommandParser::kATPrefixLen = kATPrefix.length();
const std::string ATCommandParser::kATAllowedOpChars = "? =\r\n"; // NOTE: these delimit the end of a command!

/**
 * Public Functions
*/

ATCommandParser::ATCommandParser() {}

/**
 * @brief Constructor.
 * @param[in] at_command_list_in std::vector of ATCommandDef_t's that define what AT commands are supported
 * as well as their corresponding callback functions.
*/
ATCommandParser::ATCommandParser(std::vector<ATCommandDef_t> at_command_list_in)
{
    SetATCommandList(at_command_list_in);
}

/**
 * @brief Helper function that clears existing AT commands and populates with a new list of AT Command
 * definitions. Adds a definition for AT+HELP.
 * @param[in] at_command_list_in std::vector of ATCommandDef_t's that define what AT commands are supported
 * as well as their corresponding callback functions.
*/
void ATCommandParser::SetATCommandList(std::vector<ATCommandDef_t> at_command_list_in) {
    at_command_list_.clear();
    for (ATCommandDef_t& def: at_command_list_in) {
        at_command_list_.push_back(def);
    }
    ATCommandDef_t help_def = {
        .command = "+HELP",
        .min_args = 0,
        .max_args = 100,
        .help_string = "Display this text.\r\n",
        .callback = std::bind(
            &ATCommandParser::ATHelpCallback, 
            this, 
            std::placeholders::_1, 
            std::placeholders::_2
        )
    };
    at_command_list_.push_back(help_def);
}

/**
 * @brief Destructor. Deallocates dynamically allocated memory.
*/
ATCommandParser::~ATCommandParser() {
    at_command_list_.clear(); // Note: this works as long as elements are objects and not pointers.
}

/**
 * @brief Returns the number of supported AT commands, not counting the auto-generated AT+HELP command.
 * @retval Size of at_command_list_.
*/
uint16_t ATCommandParser::GetNumATCommands() {
    return at_command_list_.size()-1; // Remove auto-generated help command from count.
}

/**
 * @brief Returns a pointer to the first ATCommandDef_t object that matches the text command provided.
 * @param[in] command String containing command text to look for.
 * @retval Pointer to corresponding ATCommandDef_t within the at_command_list_, or nullptr if not found.
*/
ATCommandParser::ATCommandDef_t * ATCommandParser::LookupATCommand(std::string command) {
    if (command.length() > kATCommandMaxLen) {
        return nullptr; // Command is too long, not supported.
    }
    for (ATCommandDef_t& def: at_command_list_) {
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

        // Command is everything between AT prefix and the first punctuation or newline.
        size_t command_end = message.find_first_of(kATAllowedOpChars, start);
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
        start+=command.length(); // Shift start to end of command.
        // Look for operator (non-alphanumeric char at end of command).
        char op = '\0';
        if (start < message.length()) {
            if (message[start] != '\r' && message[start] != '\n') {
                // Don't record line returns as op to make downstream stuff simpler.
                op = message[start];
            }
            // Ignore all non alphanumeric characters after the op character. This skips the trailing
            // \n if the op is something like "\r\n".
            while (start < message.length() && !isalnum(message[start])) {
                start += 1;
            }
        }
        // Args are everything between command and carriage return or newline.
        std::stringstream args_string(message.substr(start, message.find_first_of("\r\n", start)-start));

        std::string arg;
        std::vector<std::string> args_list;
        while(std::getline(args_string, arg, ',')) {
            args_list.push_back(arg);
        }
        size_t num_args = args_list.size();
        if ((num_args < def->min_args) || (num_args > def->max_args)) {
            printf("ATCommandParser::ParseMessage: Received incorrect number of args for command %s: got %d, expected minimum %d, maximum %d.\r\n",
                command.c_str(), num_args, def->min_args, def->max_args);
            return false;
        }
        if (def->callback) {
            bool result = def->callback(op, args_list);
            if (!result) {
                printf("ATCommandParser::ParseMessage: Call to AT Command %s with op '%c' and args %s failed.\r\n", command.c_str(), op, args_string.str().c_str());
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

bool ATCommandParser::ATHelpCallback(char op, std::vector<std::string> args) {
    printf("AT Command Help Menu:\r\n");
    for (ATCommandDef_t at_command: at_command_list_) {
        printf("%s: \r\n", at_command.command.c_str());
        printf("\t%s\r\n", at_command.help_string.c_str());
    }
    return true;
}