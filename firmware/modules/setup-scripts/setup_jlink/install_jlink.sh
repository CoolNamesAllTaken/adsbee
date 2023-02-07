#!/bin/bash

jlink_linux_url=https://www.segger.com/downloads/jlink/JLink_Linux_x86_64.deb


mkdir temp

wget -O temp/jlink_linux.deb --post-data 'accept_license_agreement=accepted&non_emb_ctr=confirmed&submit=Download+software' $jlink_linux_url
# Note that dpkg installs stuff into opt/SEGGER.
sudo dpkg -i temp/jlink_linux.deb

rm -rf temp

# Note that this might throw an error about reloading stuff, (I think it's related to udev rules?), still seems to work OK.
