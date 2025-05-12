## install\_jlink.sh
This file installs the JLink toolchain to /opt/SEGGER/JLink (symlink to /opt/SEGGER/SpecificJLinkVersion).

Note that something about the install may throw an error about being unable to reload, still seems to work OK anyways (I think the error is related to udev rules).

A source with some [good info](https://blog.feabhas.com/2019/07/using-a-raspberry-pi-as-a-remote-headless-j-link-server/).

## install\_dependencies.sh
Installs libxcv dependencies neede by JLink. You may need to run `sudo apt fix-broken install` after running this since I don't think all the dependencies are there. 
