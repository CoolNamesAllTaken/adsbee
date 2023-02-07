#include "gtest/gtest.h"
#include "scbs_comms.hh"
#include <string.h>

#define FLOAT_RELTOL 0.0005f

TEST(BSPacketChecksum, BSDIS) {
	// Examples generated with NMEA checksum calculator: https://nmeachecksum.eqth.net/
	char str_buf[BSPacket::kMaxPacketLen] = "$BSDIS,0*53";
	BSPacket test_packet = BSPacket(str_buf);
	uint16_t expected_checksum = strtoul("53", NULL, 16);
	ASSERT_EQ(expected_checksum, test_packet.CalculateChecksum());

	memset(str_buf, '\0', BSPacket::kMaxPacketLen);
	strcpy(str_buf, "$BSDIS,48789729587*5F");
	test_packet = BSPacket(str_buf);
	expected_checksum = strtoul("5F", NULL, 16);
	ASSERT_EQ(expected_checksum, test_packet.CalculateChecksum());
}

TEST(BSPacketChecksum, BSSRD) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSSRD,53,0285*5D";
	BSPacket test_packet = BSPacket(str_buf);
	uint16_t expected_checksum = strtoul("5D", NULL, 16);
	ASSERT_EQ(expected_checksum, test_packet.CalculateChecksum());
}

TEST(BSPacketChecksum, BSMRD) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSMRD,843,hi,my,name,is,frank,and,"
	"I,work,in,a,button,factory,yessiree,I,got,a,wife,three,kids,and*58";
	BSPacket test_packet = BSPacket(str_buf);
	uint16_t expected_checksum = strtoul("58", NULL, 16);
	ASSERT_EQ(expected_checksum, test_packet.CalculateChecksum());
}

TEST(BSPacketIsValid, ValidPacket) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSSRD,53,0285*5D";
	BSPacket test_packet = BSPacket(str_buf);
	ASSERT_TRUE(test_packet.IsValid());
}

TEST(BSPacketIsValid, BadTransmittedChecksum) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSSRD,53,0285*5C";
	BSPacket test_packet = BSPacket(str_buf);
	ASSERT_FALSE(test_packet.IsValid());
}

TEST(BSPacketIsValid, InjectedGibberish) {
	// Corrupted packet contents
	char str_buf[BSPacket::kMaxPacketLen] = "$BSSRD,53,02asgasgasgaewrrhgeg85*5D";
	BSPacket test_packet = BSPacket(str_buf);
	ASSERT_FALSE(test_packet.IsValid());
}

TEST(BSPacketIsValid, NoEndToken) {
	// '*' suffix token not transmitted
	char str_buf[BSPacket::kMaxPacketLen] = "$BSSRD,53,02855D";
	BSPacket test_packet = BSPacket(str_buf);
	ASSERT_FALSE(test_packet.IsValid());
}

TEST(BSPacketIsValid, NoStartToken) {
	// '$' prefix token not transmitted
	char str_buf[BSPacket::kMaxPacketLen] = "BSSRD,53,0285*5D";
	BSPacket test_packet = BSPacket(str_buf);
	ASSERT_FALSE(test_packet.IsValid());
}

TEST(TestBSPacketConstructor, SenseHeader) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSSRD,53,0285*5D";
	BSPacket test_packet = BSPacket(str_buf);
	ASSERT_EQ(test_packet.GetPacketType(), BSPacket::SRD);
}

TEST(DISPacketConstructor, Basic) {
	char str_buf[BSPacket::kMaxPacketLen];
	DISPacket packet = DISPacket(53);
	ASSERT_EQ(packet.last_cell_id, 53);
	packet.ToString(str_buf);
	ASSERT_STREQ(str_buf, "$BSDIS,53*65");

	packet = DISPacket((char *)"$BSDIS,1*52\r\n");
	ASSERT_EQ(packet.last_cell_id, 1);
}

TEST(DISPacketConstructor, StringToStringValid) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSDIS,56*60";
	DISPacket test_packet = DISPacket(str_buf);
	ASSERT_EQ(test_packet.GetPacketType(), BSPacket::DIS);
	ASSERT_TRUE(test_packet.IsValid());
	ASSERT_EQ(test_packet.last_cell_id, 56);

	char str_out_buf[BSPacket::kMaxPacketLen];
	test_packet.ToString(str_out_buf);
	ASSERT_STREQ(str_out_buf, "$BSDIS,56*60");
}

TEST(DISPacketConstructor, StringToStringInvalid) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSDIS,56safd*60";
	DISPacket test_packet = DISPacket(str_buf);
	ASSERT_EQ(test_packet.GetPacketType(), BSPacket::DIS);
	ASSERT_FALSE(test_packet.IsValid());
	ASSERT_EQ(test_packet.last_cell_id, 0);

	char str_out_buf[BSPacket::kMaxPacketLen];
	test_packet.ToString(str_out_buf);
	ASSERT_STREQ(str_out_buf, "$BSDIS,0*53"); // value of last_cell_id should be unread
}

TEST(MWRPacketConstructor, StringToStringValid) {
	char str_buf[BSPacket::kMaxPacketLen];
	MWRPacket packet = MWRPacket(0x78, (char *)"potatoes");
	ASSERT_EQ(packet.reg_addr, 0x78u);
	ASSERT_STREQ(packet.value, "potatoes");
	packet.ToString(str_buf);
	ASSERT_STREQ(str_buf, "$BSMWR,78,potatoes*51");

	packet = MWRPacket((char *)"$BSMWR,09234,elbowsyay*04\r\n");
	ASSERT_TRUE(packet.IsValid());
	ASSERT_EQ(packet.reg_addr, 0x09234u);
	ASSERT_STREQ(packet.value, "elbowsyay");
}

TEST(MWRPacketConstructor, StringToStringInvalid) {
	MWRPacket packet = MWRPacket((char *)"$BSMWR,09234,elasgahateatht44bowsyay*04\r\n");
	ASSERT_FALSE(packet.IsValid());
	ASSERT_EQ(packet.reg_addr, 0x00u);
	ASSERT_STREQ(packet.value, "");

	char str_buf[BSPacket::kMaxPacketLen];
	packet.ToString(str_buf);
	ASSERT_STREQ(str_buf, "$BSMWR,0,*69");
}

TEST(MWRPacketConstructor, StringTooLong) {
	MWRPacket packet = MWRPacket(
		(char *)"$BSMWR,09234,elasgahateatht44bowsasdggggggggggggeadsgaerwheatrh"
		"taedrshatethaeshgashbashfashrfbgashgbashbasbhggshlasgahateatht44bowsasd"
		"ggggggggggggeadsgaerwheatrhtaedrshatethaeshgashbashfashrfbgashgbashbasb"
		"hggshyayay*04\r\n"
	);
	ASSERT_FALSE(packet.IsValid());
	char str_buf[BSPacket::kMaxPacketLen];
	packet.ToString(str_buf);
	ASSERT_STREQ(str_buf, "$BSMWR,0,*69");
}

TEST(MRDPacketConstructor, FromValues) {
	char values_in[MRDPacket::kMaxNumValues][BSPacket::kMaxPacketFieldLen] = {"beefcakes", "twelve", "toodles"};
	MRDPacket packet = MRDPacket(0x843u, values_in, 3);
	ASSERT_EQ(packet.reg_addr, 0x843u);
	ASSERT_EQ(packet.num_values, 3);
	ASSERT_STREQ(packet.values[0], "beefcakes");
	ASSERT_STREQ(packet.values[1], "twelve");
	ASSERT_STREQ(packet.values[2], "toodles");
}

TEST(MRDPacketConstructor, NoValues) {
	char values_in[][BSPacket::kMaxPacketFieldLen] = {
	};
	MRDPacket packet = MRDPacket(0x843u, values_in, 3);
	ASSERT_EQ(packet.reg_addr, 0x843u);
	ASSERT_EQ(packet.num_values, 3);
	ASSERT_STREQ(packet.values[0], "");
	ASSERT_STREQ(packet.values[1], "");
	ASSERT_STREQ(packet.values[2], "");
}

TEST(MRDPacketToString, ValuesTooLong) {
	char values_in[][BSPacket::kMaxPacketFieldLen] = {
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn",
		"thisisaverylongstrn"
	};
	MRDPacket packet = MRDPacket(0x843u, values_in, 20);
	char str_buf[400];
	packet.ToString(str_buf);
	ASSERT_STREQ(str_buf, "$BSMRD,843,thisisaverylongstrn,thisisaverylongstrn,"
		"thisisaverylongstrn,thisisaverylongstrn,thisisaverylongstrn,thisisave"
		"rylongstrn,thisisaverylongstrn,thisisaverylongstrn,thisisaverylongstr"
		"n*01");
}

TEST(MRDPacketConstructor, FromStringBasic) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSMRD,843,hi,my,name,is,frank,and,"
	"I,work,in,a,button,factory,yessiree,I,got,a,wife,three,kids,and*58";
	MRDPacket packet = MRDPacket(str_buf);
	ASSERT_TRUE(packet.IsValid());
	ASSERT_EQ(packet.reg_addr, 0x843u);
	ASSERT_EQ(packet.num_values, 20);
	ASSERT_STREQ(packet.values[0], "hi");
	ASSERT_STREQ(packet.values[1], "my");
	ASSERT_STREQ(packet.values[2], "name");
	ASSERT_STREQ(packet.values[3], "is");
	ASSERT_STREQ(packet.values[4], "frank");
	ASSERT_STREQ(packet.values[5], "and");
	ASSERT_STREQ(packet.values[6], "I");
	ASSERT_STREQ(packet.values[7], "work");
	ASSERT_STREQ(packet.values[8], "in");
	ASSERT_STREQ(packet.values[9], "a");
	ASSERT_STREQ(packet.values[10], "button");
	ASSERT_STREQ(packet.values[11], "factory");
	ASSERT_STREQ(packet.values[12], "yessiree");
	ASSERT_STREQ(packet.values[13], "I");
	ASSERT_STREQ(packet.values[14], "got");
	ASSERT_STREQ(packet.values[15], "a");
	ASSERT_STREQ(packet.values[16], "wife");
	ASSERT_STREQ(packet.values[17], "three");
	ASSERT_STREQ(packet.values[18], "kids");
	ASSERT_STREQ(packet.values[19], "and");
}

TEST(MRDPacketConstructor, FromStringTooMany) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSMRD,843,hi,my,name,is,frank,and,"
	"I,work,in,a,button,factory,yessiree,I,got,a,wife,three,kids,and,a,family*2F";
	MRDPacket packet = MRDPacket(str_buf);
	ASSERT_FALSE(packet.IsValid());
	ASSERT_EQ(packet.reg_addr, 0x843u); // ok, gets to this before failing out
	ASSERT_EQ(packet.num_values, 20); // should rail to kMaxNumValues
}

TEST(MRDPacketConstructor, FromStringInvalid) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSMRD,843,hi,my,name,is,frank,and,"
	"I,work,in,a,button,factory,yessiree,I,got,a,wife,three,kids,and,a,family*33";
	MRDPacket packet = MRDPacket(str_buf);
	ASSERT_FALSE(packet.IsValid());
	ASSERT_EQ(packet.reg_addr, 0x00u);
	ASSERT_EQ(packet.num_values, 0);
	for (uint16_t i = 0; i < MRDPacket::kMaxNumValues; i++) {
		ASSERT_STREQ(packet.values[i], "");
	}
}

TEST(MRDPacketConstructor, FromStringLong) {
	char str_buf[400] = "$BSMRD,843,thisisaverylongstrn,thisisaverylongstrn,this"
		"isaverylongstrn,thisisaverylongstrn,thisisaverylongstrn,thisisaverylong"
		"strn,thisisaverylongstrn,thisisaverylongstrn,thisisaverylongstrn*01";
	MRDPacket packet = MRDPacket(str_buf);
	ASSERT_TRUE(packet.IsValid());
	ASSERT_EQ(packet.reg_addr, 0x843u);
	ASSERT_EQ(packet.num_values, 9);
	for (uint16_t i = 0; i < 9; i++) {
		ASSERT_STREQ(packet.values[i], "thisisaverylongstrn");
	}
}

TEST(MRDPacketConstructor, FromStringTooLong) {
	char str_buf[400] = "$BSMRD,843,thisisaverylongstrn,thisisaverylongstrn,this"
		"isaverylongstrn,thisisaverylongstrn,thisisaverylongstrn,thisisaverylong"
		"strn,thisisaverylongstrn,thisisaverylongstrn,thisisaverylongstrn,thisis"
		"averylongstrn*01";
	MRDPacket packet = MRDPacket(str_buf);
	ASSERT_FALSE(packet.IsValid());
	ASSERT_EQ(packet.reg_addr, 0x00u);
	ASSERT_EQ(packet.num_values, 0);
}

TEST(SWRPacketConstructor, ValuesToStringTooLong) {
	SWRPacket packet = SWRPacket(53, 0xDEADBEEF, (char *)"hi there sir what is up");
	char str_buf[BSPacket::kMaxPacketLen];
	packet.ToString(str_buf);
	ASSERT_STREQ(str_buf, "$BSSWR,53,DEADBEEF,hi there sir what i*09");
}

TEST(SWRPacketConstructor, FromStringValid) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSSWR,53,DEADBEEF,hi there sir what i*09";
	SWRPacket packet = SWRPacket(str_buf);
	ASSERT_TRUE(packet.IsValid());
	ASSERT_EQ(packet.cell_id, 53);
	ASSERT_EQ(packet.reg_addr, 0xDEADBEEF);
	ASSERT_STREQ(packet.value, "hi there sir what i");
}

TEST(SRDPacketConstructor, ValuesToString) {
	SRDPacket packet = SRDPacket(67, 0xBEEFBEFA);
	ASSERT_EQ(packet.cell_id, 67);
	ASSERT_EQ(packet.reg_addr, 0xBEEFBEFA);
	char str_buf[BSPacket::kMaxPacketLen];
	packet.ToString(str_buf);
	ASSERT_STREQ(str_buf, "$BSSRD,67,BEEFBEFA*51");
}

TEST(SRDPacketConstructor, FromStringValid) {
	char str_buf[BSPacket::kMaxPacketLen] = "$BSSRD,67,BEEFBEFA*51";
	SRDPacket packet = SRDPacket(str_buf);
	ASSERT_TRUE(packet.IsValid());
	ASSERT_EQ(packet.cell_id, 67);
	ASSERT_EQ(packet.reg_addr, 0xBEEFBEFA);
}

TEST(SRSPacketConstructor, ValuesToString) {
	SRSPacket packet = SRSPacket(36, (char *)"test message 123");
	ASSERT_EQ(packet.cell_id, 36);
	ASSERT_STREQ(packet.value, "test message 123");
	char str_buf[BSPacket::kMaxPacketLen];
	packet.ToString(str_buf);
	ASSERT_STREQ(str_buf, "$BSSRS,36,test message 123*0B");
}