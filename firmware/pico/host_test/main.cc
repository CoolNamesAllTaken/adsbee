#include "gtest/gtest.h"

#include "main.hh"
#include "comms.hh" // For comms manager required by ADSBPacket for error reporting.

// CommsManager comms_manager = CommsManager({});

int main(int argc, char *argv[])
{
	::testing::InitGoogleTest(&argc, argv);
	return RUN_ALL_TESTS();
}