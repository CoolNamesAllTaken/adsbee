# rfPacketRx

---

Project Setup using the System Configuration Tool (SysConfig)
-------------------------
The purpose of SysConfig is to provide an easy to use interface for configuring
drivers, RF stacks, and more. The .syscfg file provided with each example
project has been configured and tested for that project. Changes to the .syscfg
file may alter the behavior of the example away from default. Some parameters
configured in SysConfig may require the use of specific APIs or additional
modifications in the application source code. More information can be found in
SysConfig by hovering over a configurable and clicking the question mark (?)
next to it's name.

Example Summary
---------------
The Packet RX example illustrates how to do simple packet RX using the
RF driver. This example is meant to be used with the Packet TX example or
SmartRF Studio. For every packet received, CONFIG_PIN_RLED is toggled.
The frequency and other RF settings can be modified using SmartRF Studio.

Peripherals Exercised
---------------------
* `CONFIG_PIN_RLED` - Toggled when data is received over the RF interface

Resources & Jumper Settings
---------------------------
> If you're using an IDE (such as CCS or IAR), please refer to Board.html in your project
directory for resources used and board-specific jumper settings. Otherwise, you can find
Board.html in the directory &lt;SDK_INSTALL_DIR&gt;/source/ti/boards/&lt;BOARD&gt;.

Board Specific Settings
-----------------------
1. The default frequency is:
    - 433.92 MHz for the CC1352P-4-LAUNCHXL
    - 2440 MHz on the CC26X2R1-LAUNCHXL
    - 868.0 MHz for other launchpads  
NOTE: In order to change frequency, modify the ti_radio_config.c file. This can be
done using the code export feature in Smart RF Studio, or directly in the file
2. On the CC1352P1 the high PA is enabled (high output power) for all
Sub-1 GHz modes by default.
3. On the CC1352P-2 and CC1352P-4 the high PA operation for Sub-1 GHz modes is not supported

Example Usage
-------------
Run the example. On another board, run the EasyLink TX example.
CONFIG_PIN_RLED is toggled when data with CRC OK is received.

Application Design Details
--------------------------
This examples consists of a single task and the exported SmartRF Studio radio
settings.

When the task is executed it:

1. Configures the radio for Proprietary mode
2. Gets access to the radio via the RF drivers RF_open
3. Sets up the radio using CMD_PROP_RADIO_DIV_SETUP command
4. Defines a data queue to handle received data
5. Sets the frequency using CMD_FS command
6. Sends the CMD_PROP_RX command to start receiving data
7. Once data with CRC OK is received we toggle the
   CONFIG_PIN_RLED and re-enter RX with the CMD_PROP_RX command
