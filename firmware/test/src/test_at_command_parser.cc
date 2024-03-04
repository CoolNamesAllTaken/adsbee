#include "gtest/gtest.h"
#include "at_command_parser.hh"
#include "string.h"

bool callback1_was_called = false;
bool callback2_was_called = false;

bool Callback1(std::vector<std::string>) {
    callback1_was_called = true;
    return true;
}

bool Callback2(std::vector<std::string>) {
    callback2_was_called = true;
    return true;
}

TEST(ATCommandParser, SingleATCommand) {
    std::vector<ATCommandParser::ATCommandDef_t> at_command_list;
    ATCommandParser::ATCommandDef_t def = {
        .command = "TEST",
        .min_args = 1,
        .max_args = 1,
        .help_string = "This is a test.",
        .callback = Callback1
    };
    assert(at_command_list.size() == 0);
    at_command_list.push_back(def);
    assert(at_command_list.size() == 1);
    ATCommandParser parser = ATCommandParser(at_command_list);
    assert(parser.GetNumATCommands() == 1);
    
    // Looking up a fake command should fail.
    assert(parser.LookupATCommand("Blah") == nullptr);

    // Looking up a real command should work.
    ATCommandParser::ATCommandDef_t * returned_command = parser.LookupATCommand("TEST");
    assert(returned_command->command.compare("TEST") == 0);
    callback1_was_called = false;
    std::vector<std::string> args = {"arg1", "arg2"};
    returned_command->callback(args);
    assert(callback1_was_called);
    assert(returned_command->help_string.compare("This is a test.") == 0);
}

ATCommandParser BuildExampleParser1() {
    std::vector<ATCommandParser::ATCommandDef_t> at_command_list;
    ATCommandParser::ATCommandDef_t def = {
        .command = "TEST",
        .min_args = 1,
        .max_args = 1,
        .help_string = "This is a test.",
        .callback = Callback1
    };
    at_command_list.push_back(def);
    def.command = "CFG";
    def.min_args = 1;
    def.max_args = 3;
    def.help_string = "Configuration. Takes between 1 and 3 arguments.";
    def.callback = Callback2;
    at_command_list.push_back(def);
    return ATCommandParser(at_command_list);
}

TEST (ATCommandParser, TwoATCommands) {
    ATCommandParser parser = BuildExampleParser1();
    assert(parser.GetNumATCommands() == 2);

    // Looking up a fake command should fail.
    assert(parser.LookupATCommand("Potatoes") == nullptr);

    // Looking up real command 1 should work.
    ATCommandParser::ATCommandDef_t * returned_command = parser.LookupATCommand("TEST");
    assert(returned_command->command.compare("TEST") == 0);
    callback1_was_called = false;
    std::vector<std::string> args1 = {"arg1", "arg2"};
    returned_command->callback(args1);
    assert(callback1_was_called);
    assert(returned_command->help_string.compare("This is a test.") == 0);

    // Looking up real command 2 should work.
    returned_command = parser.LookupATCommand("CFG");
    assert(returned_command->command.compare("CFG") == 0);
    callback2_was_called = false;
    std::vector<std::string> args2 = {"arg1", "arg2"};
    returned_command->callback(args2);
    assert(callback2_was_called);
    assert(returned_command->help_string.compare("Configuration. Takes between 1 and 3 arguments.") == 0);
}