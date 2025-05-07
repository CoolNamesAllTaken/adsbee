#!/bin/bash

sysconfig_tool_url=https://dr-download.ti.com/software-development/ide-configuration-compiler-or-debugger/MD-nsUM6f7Vvb/1.23.1.4034/sysconfig-1.23.1_4034-setup.run

sudo apt -y install cmake git
sudo DEBIAN_FRONTEND=noninteractive apt -y --fix-broken install

# Install SYSCONFIG tool.
mkdir temp
wget -O temp/sysconfig-setup.run $sysconfig_tool_url
chmod +x temp/sysconfig-setup.run
sudo yes | ./temp/sysconfig-setup.run
rm -rf temp
