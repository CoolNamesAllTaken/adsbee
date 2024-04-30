#include "at_command_parser.hh"

#include <sstream> // stringstream for splitting using getline()
#include <cstring> // for memcpy

/**
 * Initialize static const member variables.
*/
const char ATCommandParser::kATPrefix[] = "AT";
const uint16_t ATCommandParser::kATPrefixLen = sizeof(ATCommandParser::kATPrefix)-1; // Remove EOS character.
const char ATCommandParser::kATAllowedOpChars[] = "? =\r\n"; // NOTE: these delimit the end of a command!
const char ATCommandParser::kATMessageEndStr[] = "\r\n";

/**
 * Public Functions
*/

ATCommandParser::ATCommandParser() {}

/**
 * @brief Constructor.
 * @param[in] at_command_list_in std::vector of ATCommandDef_t's that define what AT commands are supported
 * as well as their corresponding callback functions.
*/
ATCommandParser::ATCommandParser(const ATCommandDef_t * at_command_list_in)
{
    SetATCommandList(at_command_list_in);
}

/**
 * @brief Helper function that clears existing AT commands and populates with a new list of AT Command
 * definitions. Adds a definition for AT+HELP.
 * @param[in] at_command_list_in Array of ATCommandDef_t's that define what AT commands are supported
 * as well as their corresponding callback functions.
*/
void ATCommandParser::SetATCommandList(const ATCommandDef_t * at_command_list_in) {
    if (at_command_list_ != nullptr) {
        free(at_command_list_);
    }
    // Allocate space for the AT commands, with an extra slot for HELP at the end.
    num_at_commands_ = sizeof(at_command_list_in) / sizeof(ATCommandDef_t) + 1;
    uint16_t at_command_list_len_bytes = num_at_commands_ * sizeof(ATCommandDef_t);
    at_command_list_ = (ATCommandDef_t *)malloc(at_command_list_len_bytes);
    // Copy in AT commands provided to SetATCommandList.
    memcpy((uint8_t *)at_command_list_, (uint8_t *)at_command_list_in, at_command_list_len_bytes-sizeof(ATCommandDef_t));
    // Add in +HELP command.
    at_command_list_[num_at_commands_] = ATCommandDef_t();
    ATCommandDef_t &help_command = at_command_list_[num_at_commands_];
    strncpy(help_command.command_buf, "+HELP", kATCommandMaxLen-1);
    help_command.command = std::string_view(help_command.command_buf);
    strncpy(help_command.help_string_buf, "Display this text.\r\n", kHelpStringMaxLen-1);
    help_command.help_string = std::string_view(help_command.help_string);
    
    // {
    //     .command_buf = "+HELP",
    //     .command = std::string_view(),
    //     .min_args = 0,
    //     .max_args = 100,
    //     .help_string_buf = "Display this text.\r\n",
    //     .help_string = std::string_view(),
    //     .callback = std::bind(
    //         &ATCommandParser::ATHelpCallback, 
    //         this, 
    //         std::placeholders::_1, 
    //         std::placeholders::_2
    //     )
    // };
    
    
}

/**
 * @brief Destructor. Deallocates dynamically allocated memory.
*/
ATCommandParser::~ATCommandParser() {
    free(at_command_list_);
    // at_command_list_.clear(); // Note: this works as long as elements are objects and not pointers.
}

/**
 * @brief Returns the number of supported AT commands, not counting the auto-generated AT+HELP command.
 * @retval Size of at_command_list_.
*/
uint16_t ATCommandParser::GetNumATCommands() {
    return sizeof(at_command_list_)/sizeof(ATCommandDef_t); // Remove auto-generated help command from count.
}

/**
 * @brief Returns a pointer to the first ATCommandDef_t object that matches the text command provided.
 * @param[in] command String containing command text to look for.
 * @retval Pointer to corresponding ATCommandDef_t within the at_command_list_, or nullptr if not found.
*/
ATCommandParser::ATCommandDef_t * ATCommandParser::LookupATCommand(std::string_view command) {
    if (command.length() > kATCommandMaxLen) {
        return nullptr; // Command is too long, not supported.
    }
    for (uint16_t i = 0; i < num_at_commands_; i++) {
        ATCommandDef_t &def = at_command_list_[i];
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
bool ATCommandParser::ParseMessage(std::string_view message) {
    // Message should start with "AT"
    std::size_t start = message.find(kATPrefix);
    if (start == std::string::npos) {
        printf("ATCommandParser::ParseMessage: Unable to find AT prefix in string %.*s.\r\n", 
            message.length(), message.data());
        return false;
    }

    while (start != std::string::npos) {
        start += kATPrefixLen; // Start after the AT prefix.

        // Command is everything between AT prefix and the first punctuation or newline.
        size_t command_end = message.find_first_of(kATAllowedOpChars, start);
        std::string_view command = message.substr(
            start, command_end == std::string::npos ? std::string::npos : command_end - start);
        if (command.length() == 0) {
            printf("ATCommandParser::ParseMessage: Can't parse 0 length command in string %.*s.\r\n", 
                message.length(), message.data());
            return false;
        }
        // Try matching the command text with an AT command definition.
        ATCommandDef_t * def = LookupATCommand(command);
        if (def == nullptr) {
            printf("ATCommandParser::ParseMessage: Unable to match AT command %.*s.\r\n", 
                command.length(), command.data());
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
            // \n if the op is something like "\r\n". Don't ignore commas which might delimit blank args.
            while (start < message.length() && !isalnum(message[start]) && message[start] != ',') {
                start += 1;
            }
        }
        // Args are everything between command and carriage return or newline.
        std::string_view args_string = message.substr(start, message.find_first_of("\r\n", start)-start);

        std::string_view arg;
        std::vector<std::string_view> args_list;
        size_t arg_start = 0;
        size_t arg_end = args_string.find(kArgDelimiter);
        while(arg_end != std::npos) {
            std::string_view arg = args_string.substr(arg_start, arg_end-arg_start);
            args_list.push_back(arg);
            arg_start = arg_end;
            arg_end = args_string.find(kArgDelimiter, arg_end);
        }
        // Cover the trailing empty argument special case.
        if (args_string[args_string.length()-1] == ',') {
            args_list.push_back("");
        }
        
        size_t num_args = args_list.size();
        if ((num_args < def->min_args) || (num_args > def->max_args)) {
            printf("ATCommandParser::ParseMessage: Received incorrect number of args for command %.*s: got %d, expected minimum %d, maximum %d.\r\n",
                command.length(), command.data(), num_args, def->min_args, def->max_args);
            return false;
        }
        if (def->callback) {
            bool result = def->callback(op, args_list);
            if (!result) {
                printf("ATCommandParser::ParseMessage: Call to AT Command %.*s with op '%c' and args %.*s failed.\r\n", 
                command.length(), command.data(), op, args_string.length(), args_string.data());
                return false;
            }
        } else {
            printf("ATCommandParser::ParseMessage: Received a call to AT command %.*s with no corresponding callback function.\r\n", 
            command.length(), command.data());
        }

        // Look for the next AT command. Skip to next AT prefix after the newline.
        start = message.find(kATPrefix, start);
    }

    return true;
}

inline bool ATCommandParser::ArgToNum(std::string_view arg, auto &number, uint16_t base) {
    number = 0;
    auto result = std::from_chars(arg.data(), arg.data() + arg.size(), number, base);
    if (result.ec == std::errc()) {
        return false;
    }
    return true;
}

/**
 * Private Functions
*/

bool ATCommandParser::ATHelpCallback(char op, std::vector<std::string_view> args) {
    printf("AT Command Help Menu:\r\n");
    for (uint16_t i = 0; i < num_at_commands_; i++) {
        ATCommandDef_t at_command = at_command_list_[i];
        printf("%.*s: \r\n", at_command.command.length(), at_command.command.data());
        printf("\t%.*s\r\n", at_command.help_string.length(), at_command.help_string.data());
    }
    return true;
}