#!/usr/bin/env python3
# Derived from pad_checksum in the Pico SDK, which carries the following
# LICENSE.txt:
# Copyright 2020 (c) 2020 Raspberry Pi (Trading) Ltd.
#
# Redistribution and use in source and binary forms, with or without modification, are permitted provided that the
# following conditions are met:
#
# 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following
#    disclaimer.
#
# 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following
#    disclaimer in the documentation and/or other materials provided with the distribution.
#
# 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products
#    derived from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES,
# INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
# WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
# THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

import argparse
import binascii
import struct
import sys

parser = argparse.ArgumentParser()
parser.add_argument("ifile", help="Input file (binary)")
parser.add_argument("ofile", help="Output file (assembly)")
parser.add_argument("--section", default="boot3", required=False, help="Section name in assembly file to be created. Used for linking.")
args = parser.parse_args()

try:
    idata = open(args.ifile, "rb").read()
except:
    sys.exit(f"Could not open input file '{args.ifile}'")

odata = idata

try:
    print(f"Converting {args.ifile} to {args.ofile} with section name {args.section}.")
    with open(args.ofile, "w") as ofile:
        ofile.write(f"// ASM-ified version of: {args.ifile}\n\n")
        ofile.write(".cpu cortex-m0plus\n")
        ofile.write(".thumb\n\n")
        ofile.write(f".section .{args.section}, \"ax\"\n\n")
        for offs in range(0, len(odata), 16):
            chunk = odata[offs:min(offs + 16, len(odata))]
            ofile.write(".byte {}\n".format(", ".join("0x{:02x}".format(b) for b in chunk)))
except:
    sys.exit("Could not open output file '{}'".format(args.ofile))