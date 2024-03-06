#include "gtest/gtest.h"
#include "at_command_parser.hh"
#include "string.h"

bool callback1_was_called = false;
bool callback2_was_called = false;

bool Callback1(char op, std::vector<std::string>) {
    callback1_was_called = true;
    return true;
}

bool Callback2(char op, std::vector<std::string>) {
    callback2_was_called = true;
    return true;
}

TEST(ATCommandParser, SingleATCommand) {
    std::vector<ATCommandParser::ATCommandDef_t> at_command_list;
    ATCommandParser::ATCommandDef_t def = {
        .command = "+TEST",
        .min_args = 0,
        .max_args = 1,
        .help_string = "This is a test.",
        .callback = Callback1
    };
    ASSERT_TRUE(at_command_list.size() == 0);
    at_command_list.push_back(def);
    ASSERT_TRUE(at_command_list.size() == 1);
    ATCommandParser parser = ATCommandParser(at_command_list);
    ASSERT_TRUE(parser.GetNumATCommands() == 1);
    
    // Looking up a fake command should fail.
    ASSERT_TRUE(parser.LookupATCommand("+Blah") == nullptr);

    // Looking up a real command should work.
    ATCommandParser::ATCommandDef_t * returned_command = parser.LookupATCommand("+TEST");
    ASSERT_NE(returned_command, nullptr);
    ASSERT_TRUE(returned_command->command.compare("+TEST") == 0);
    callback1_was_called = false;
    std::vector<std::string> args = {"arg1", "arg2"};
    returned_command->callback('=', args);
    ASSERT_TRUE(callback1_was_called);
    ASSERT_TRUE(returned_command->help_string.compare("This is a test.") == 0);
}

ATCommandParser BuildExampleParser1() {
    std::vector<ATCommandParser::ATCommandDef_t> at_command_list;
    ATCommandParser::ATCommandDef_t def = {
        .command = "+TEST",
        .min_args = 0,
        .max_args = 1,
        .help_string = "This is a test.",
        .callback = Callback1
    };
    at_command_list.push_back(def);
    def.command = "+CFG";
    def.min_args = 1;
    def.max_args = 3;
    def.help_string = "Configuration. Takes between 1 and 3 arguments.";
    def.callback = Callback2;
    at_command_list.push_back(def);
    return ATCommandParser(at_command_list);
}

TEST(ATCommandParser, HelpString) {
    ATCommandParser parser = BuildExampleParser1();
    ASSERT_TRUE(parser.ParseMessage("AT+HELP\r\n"));
}

TEST(ATCommandParser, TwoATCommands) {
    ATCommandParser parser = BuildExampleParser1();
    ASSERT_TRUE(parser.GetNumATCommands() == 2);

    // Looking up a fake command should fail.
    ASSERT_TRUE(parser.LookupATCommand("+Potatoes") == nullptr);

    // Looking up real command 1 should work.
    ATCommandParser::ATCommandDef_t * returned_command = parser.LookupATCommand("+TEST");
    ASSERT_NE(returned_command, nullptr);
    ASSERT_TRUE(returned_command->command.compare("+TEST") == 0);
    callback1_was_called = false;
    std::vector<std::string> args1 = {"arg1", "arg2"};
    returned_command->callback('=', args1);
    ASSERT_TRUE(callback1_was_called);
    ASSERT_TRUE(returned_command->help_string.compare("This is a test.") == 0);

    // Looking up real command 2 should work.
    returned_command = parser.LookupATCommand("+CFG");
    ASSERT_NE(returned_command, nullptr);
    ASSERT_TRUE(returned_command->command.compare("+CFG") == 0);
    callback2_was_called = false;
    std::vector<std::string> args2 = {"arg1", "arg2"};
    returned_command->callback('=', args2);
    ASSERT_TRUE(callback2_was_called);
    ASSERT_TRUE(returned_command->help_string.compare("Configuration. Takes between 1 and 3 arguments.") == 0);
}

TEST(ATCommandParser, RejectMessageWithNoAT) {
    ATCommandParser parser = BuildExampleParser1();

    ASSERT_FALSE(parser.ParseMessage("Potatoes potatoes potatoes I love potatoes."));
    ASSERT_FALSE(parser.ParseMessage("A T just kidding."));
}

TEST(ATCommandParser, RejectMessageWithZeroLengthCommand) {
    ATCommandParser parser = BuildExampleParser1();

    ASSERT_FALSE(parser.ParseMessage("AT+ other words"));
    ASSERT_FALSE(parser.ParseMessage("AT+,other words"));
    ASSERT_FALSE(parser.ParseMessage("AT+=CFG"));
    ASSERT_FALSE(parser.ParseMessage("AT+\n"));
}

TEST(ATCommandParser, RejectMessageWithCommandTooLong) {
    // Build a parser that contains a command that is too long.
    std::vector<ATCommandParser::ATCommandDef_t> at_command_list;
    ATCommandParser::ATCommandDef_t def = {
        .command = "+HIHIHIHIHIHIHIHIHIHITOOLONG"
    };
    at_command_list.push_back(def);
    ATCommandParser parser = ATCommandParser(at_command_list);

    ASSERT_FALSE(parser.ParseMessage("AT+HIHIHIHIHIHIHIHIHIHITOOLONG"));
}

TEST(ATCommandParser, RejectMessageWithNoMatchingATCommand) {
    ATCommandParser parser = BuildExampleParser1();

    ASSERT_FALSE(parser.ParseMessage("AT+WRONG"));
    ASSERT_FALSE(parser.ParseMessage("AT+\r\n"));
}

TEST(ATCommandParser, RejectMessageWithIncorrectNumberOfArgs) {
    ATCommandParser parser = BuildExampleParser1();

    // AT+TEST takes between 0-1 args.
    ASSERT_FALSE(parser.ParseMessage("AT+TEST=a,b")); // two args
    ASSERT_TRUE(parser.ParseMessage("AT+TEST=a")); // one arg
    ASSERT_TRUE(parser.ParseMessage("AT+TEST")); // no args
}

/**
 * @brief Callback function that returns true if the args are "potato" or "potato,bacon"
*/
bool MustBePotatoBacon(char op, std::vector<std::string> args) {
    if (args[0].compare("potato") == 0) {
        if (args.size() == 1) {
            return true;
        } else {
            return args[1].compare("bacon") == 0;
        }
    }
    return false;
}

ATCommandParser BuildPotatoBaconParser() {
    std::vector<ATCommandParser::ATCommandDef_t> at_command_list;
    ATCommandParser::ATCommandDef_t def = {
        .command = "+POTATOBACON",
        .min_args = 1,
        .max_args = 2,
        .help_string = "Acceptable args are \"potato\" or \" potato,bacon\".\r\n",
        .callback = MustBePotatoBacon
    };
    at_command_list.push_back(def);
    return ATCommandParser(at_command_list);
}

TEST(ATCommandParser, TwoArgsPotatoBacon) {
    ATCommandParser parser = BuildPotatoBaconParser();
    ASSERT_TRUE(parser.ParseMessage("AT+POTATOBACON=potato"));
    ASSERT_FALSE(parser.ParseMessage("AT+POTATOBACON=bacon"));
    ASSERT_TRUE(parser.ParseMessage("AT+POTATOBACON=potato,bacon"));
    ASSERT_FALSE(parser.ParseMessage("AT+POTATOBACON=potato,potato"));
}

bool PickyOpCallback(char op, std::vector<std::string> args) {
    if (op == ' ' || op == '?') {
        return true;
    }
    return false;
}

TEST(ATCommandParser, PickyOpCallback) {
    std::vector<ATCommandParser::ATCommandDef_t> at_command_list;
    ATCommandParser::ATCommandDef_t def = {
        .command = "+PICKYOP",
        .min_args = 0,
        .max_args = 100,
        .help_string = "Doot doot whatever but make the op ' ' or '?'.\r\n",
        .callback = PickyOpCallback
    };
    at_command_list.push_back(def);
    ATCommandParser parser = ATCommandParser(at_command_list);
    ASSERT_FALSE(parser.ParseMessage("AT+PICKYOP=doot\r\n"));
    ASSERT_TRUE(parser.ParseMessage("AT+PICKYOP doot\r\n"));
    ASSERT_TRUE(parser.ParseMessage("AT+PICKYOP?\r\n"));
    ASSERT_FALSE(parser.ParseMessage("AT+PICKYOP\r\n"));
}