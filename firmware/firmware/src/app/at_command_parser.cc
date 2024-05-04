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
const size_t npos = -1; // Since string_view doesn't have it. Used to represent "not found".

/**
 * Public Functions
*/

ATCommandParser::ATCommandParser() {}

/**
 * @brief Constructor.
 * @param[in] at_command_list_in Array of ATCommandDef_t's that define what AT commands are supported
 * as well as their corresponding callback functions.
 * @param[in] num_at_comands_in Length of at_command_list_in.
*/
ATCommandParser::ATCommandParser(const ATCommandDef_t * at_command_list_in, uint16_t num_at_commands_in)
{
    is_valid = SetATCommandList(at_command_list_in, num_at_commands_in);
}

/**
 * @brief Helper function that clears existing AT commands and populates with a new list of AT Command
 * definitions. Adds a definition for AT+HELP.
 * @param[in] at_command_list_in Array of ATCommandDef_t's that define what AT commands are supported
 * as well as their corresponding callback functions.
 * @param[in] num_at_commands Number of elements in at_command_list_in array.
 * @retval True if set successfully, false if failed.
*/
bool ATCommandParser::SetATCommandList(const ATCommandDef_t *at_command_list_in, uint16_t num_at_commands_in) {
    // Allocate space for the AT commands, with an extra slot for HELP at the end.
    num_at_commands_ = num_at_commands_in + 1;
    at_command_list_ = new ATCommandDef_t[num_at_commands_];
    if (at_command_list_ == nullptr) {
        printf("ATCommandParser::SetATCommandList: Dynamic memory allocation failed.\r\n");
        return false;
    }
    // Copy in AT commands provided to SetATCommandList.
    for (uint16_t i = 0; i < num_at_commands_in; i++) {
        const ATCommandDef_t &command_in = at_command_list_in[i];
        at_command_list_[i] = command_in;
    }
    // Add in +HELP command.
    at_command_list_[num_at_commands_-1] = ATCommandDef_t{
        .command = std::string_view("+HELP"),
        .min_args = 0,
        .max_args = 0,
        .help_string = std::string_view("Display this text.\r\n"),
        .callback = std::bind(
            &ATCommandParser::ATHelpCallback,
            this,
            std::placeholders::_1, 
            std::placeholders::_2,
            std::placeholders::_3
        )
    };
    // Copy string_view contents into buffers and remap string_views so that the at_command_list_ doesn't have broken
    // references when stuff goes out of scope after initialization.
    for (uint16_t i = 0; i < num_at_commands_; i++) {
        if (at_command_list_[i].command.length() > kATCommandMaxLen) {
            printf(
                "ATCommandParser::SetATCommandList: AT Command String for CommandDef %d exceeds maximum length %d.\r\n",
                i, kATCommandMaxLen
            );
            return false;
        }
        strncpy(
            at_command_list_[i].command_buf,
            at_command_list_[i].command.data(),
            at_command_list_[i].command.length()
        );
        // Add EOS character to be extra safe.
        at_command_list_[i].command_buf[at_command_list_[i].command.length()] = '\0';
        // Remap string_view.
        at_command_list_[i].command = std::string_view(at_command_list_[i].command_buf);

        if (at_command_list_[i].help_string.length() > kHelpStringMaxLen) {
            printf(
                "ATCommandParser::SetATCommandList: Help String for CommandDef %d exceeds maximum length %d.\r\n",
                i, kHelpStringMaxLen
            );
            return false;
        }
        strncpy(
            at_command_list_[i].help_string_buf,
            at_command_list_[i].help_string.data(),
            at_command_list_[i].help_string.length()
        );
        // Add EOS character to be extra safe.
        at_command_list_[i].help_string_buf[at_command_list_[i].help_string.length()] = '\0';
        // Remap string_view.
        at_command_list_[i].help_string = std::string_view(at_command_list_[i].help_string_buf);
    }

    return true;
}

/**
 * @brief Destructor. Deallocates dynamically allocated memory.
*/
ATCommandParser::~ATCommandParser() {
    delete [] at_command_list_;
}

/**
 * @brief Returns the number of supported AT commands, not counting the auto-generated AT+HELP command.
 * @retval Size of at_command_list_.
*/
uint16_t ATCommandParser::GetNumATCommands() {
    return num_at_commands_; // Remove auto-generated help command from count.
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
        char args_str_buf_list[kMaxNumArgs][kArgMaxLen+1];
        std::string_view args_list[kMaxNumArgs];
        uint16_t num_args = 0;
        size_t arg_start = 0;
        size_t arg_end;
        do {
            arg_end = args_string.find(kArgDelimiter, arg_start);
            if (num_args >= kMaxNumArgs) {
                printf("ATCommandParser::ParseMessage: Too many arguments.\r\n");
                return false;
            }
            uint16_t arg_len = arg_end == npos ? args_string.length() - arg_start : arg_end-arg_start;
            if (arg_len == 0 && arg_end == npos) {
                // Special case: final argument with zero length, don't count it unless preceeded by a delimiter.
                if (args_string[args_string.length()-1] == ',') {
                    // Trailing blank argument implied by a preceeding comma.
                    args_str_buf_list[num_args][arg_len] = '\0'; // Empty string argument.
                    args_list[num_args] = std::string_view(args_str_buf_list[num_args]);
                    num_args++;
                }
                // else: No trailing argument.
                break;
            }
            memcpy(&args_str_buf_list[num_args], &args_string[arg_start], arg_len);
            args_str_buf_list[num_args][arg_len] = '\0'; // make argument safe to process into a string view
            args_list[num_args] = std::string_view(args_str_buf_list[num_args]);
            num_args++;
            arg_start = arg_end+1;
        } while(arg_end != npos);
        // Cover the trailing empty argument special case.
        // if (args_string[args_string.length()-1] == ',') {
        //     if (num_args >= kMaxNumArgs) {
        //         printf("ATCommandParser::ParseMessage: Too many arguments.\r\n");
        //         return false;
        //     }
        //     uint16_t arg_str_buf_start = num_args*(kArgMaxLen+1);
        //     args_str_buf_list[num_args][0] = '\0';
        //     args_list[num_args] = std::string_view(args_str_buf_list[num_args]);
        //     num_args++;
        // }
        
        if ((num_args < def->min_args) || (num_args > def->max_args)) {
            printf("ATCommandParser::ParseMessage: Received incorrect number of args for command %.*s: got %d, expected minimum %d, maximum %d.\r\n",
                command.length(), command.data(), num_args, def->min_args, def->max_args);
            return false;
        }
        if (def->callback) {
            bool result = def->callback(op, args_list, num_args);
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

/**
 * Private Functions
*/

bool ATCommandParser::ATHelpCallback(char op, const std::string_view args[], uint16_t num_args) {
    printf("AT Command Help Menu:\r\n");
    for (uint16_t i = 0; i < num_at_commands_; i++) {
        ATCommandDef_t at_command = at_command_list_[i];
        printf("%.*s: \r\n", at_command.command.length(), at_command.command.data());
        printf("\t%.*s\r\n", at_command.help_string.length(), at_command.help_string.data());
    }
    return true;
}