#!/bin/bash

latest_arm_none_eabi=gcc-arm-none-eabi-13.3.1
latest_arm_none_eabi_url="https://developer.arm.com/-/media/Files/downloads/gnu/13.3.rel1/binrel/arm-gnu-toolchain-13.3.rel1-x86_64-arm-none-eabi.tar.xz?rev=e434b9ea4afc4ed7998329566b764309&hash=CA590209F5774EE1C96E6450E14A3E26"

# Install dependencies.

# sudo apt -y install libncurses5 # This command doesn't work for some reason.
# Install libncurses-dev and symlink to libncursed5 instead.
sudo apt -y install libncurses-dev
sudo ln -s /usr/lib/x86_64-linux-gnu/libncurses.so.6 /usr/lib/x86_64-linux-gnu/libncurses.so.5
sudo ln -s /usr/lib/x86_64-linux-gnu/libncursesw.so.6 /usr/lib/x86_64-linux-gnu/libncursesw.so.5
sudo ln -s /usr/lib/x86_64-linux-gnu/libtinfo.so.6 /usr/lib/x86_64-linux-gnu/libtinfo.so.5

sudo apt -y install python3
sudo apt -y install python3-pip

# arm-none-eabi-gdb requires Python 3.8 for some godforsaken reason.
sudo apt -y install software-properties-common
sudo add-apt-repository -y ppa:deadsnakes/ppa
sudo apt install -y python3.8

sudo apt install -y build-essential

# Remove existing (probably outdated) install.
sudo apt remove -y gcc-arm-none-eabi

mkdir temp
wget -O temp/${latest_arm_none_eabi}.tar.xz $latest_arm_none_eabi_url

# Explicitly create the destination directory.
sudo mkdir /usr/local/$latest_arm_none_eabi

# Un-tar the files into a versioned arm-none-eabi folder in /usr/local.
# --strip-components 1 option removes the top level directory
sudo tar xfv temp/${latest_arm_none_eabi}.tar.xz -C /usr/local/$latest_arm_none_eabi --strip-components 1

# Create symlinks in /usr/bin
for file in /usr/local/${latest_arm_none_eabi}/bin/*; do
    # Get just the filename (without the directory path)
    filename=$(basename "$file")
    # Check if it's a file (not a directory)
    if [ -f "$file" ]; then
        
        # Create the symlink in /usr/bin
        sudo ln -s "$file" "/usr/bin/$filename"
        echo "Created symlink for $filename."
    else
        echo "$filename is not a valid file."
    fi
done

rm -rf temp
