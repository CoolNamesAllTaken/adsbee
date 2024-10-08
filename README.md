# ADSBee 1090

ADSBee 1090 is an open-source radio receiver and decoder for ADS-B packets transmitted by aircraft on 1090MHz. ADSBee 1090 is based on an RP2040 microcontroller, and utilizes two independent PIO blocks to find and decode ADS-B messages without the need for an FPGA. ADSBee 1090 includes a radio receiver frontend with filtering and amplification, as well as a software defined comparator circuit with an adjustable trigger threshold for customizable receive sensitivity in a diverse range of RF environments.

![ADSBee 1090 Logo](affinity/adsbee_logo/exports/adsbee_logo.png)

## Features
* Decoding of 1090MHz transponder signals (ADS-B and Mode S).
* 1x USB console input / output for changing parameters and transmitting data.
* 1x UART for transmitting data.
* 1x UART for reading GNSS data.
* Built-in EEPROM for storing nonvolatile settings.
* Feature-rich AT command set for customizing baud rates, output data protocols, signal conditioning values, etc.
* Multiple supported output protocols:
    * Raw packets
    * MAVLINK1
    * MAVLINK2
    * GDL90
    * Mode S Beast
    * CSBee (custom information rich ASCII protocol)
* 2.4GHz 802.11 radio for automatic streaming of decoded values to custom endpoints on the internet. No external compute required, just add WiFi and power!
* GNSS module connector for MLAT and ground station location information.
* Low(ish) power draw.

## Purchasing and Support
ADSBee 1090 is a product of Pants for Birds LLC. To learn more about the project or purchase a device, please visit [pantsforbirds.com/adsbee-1090](https://pantsforbirds.com/adsbee-1090).

## General Architecture
ADSBee 1090 utilizes some basic RF hardware (SAW filters, LNA, logarithmic power detector) to amplify the received pulse-position-modulated ADS-B waveform into a pulse train that is conditioned by a comparator and fed to a PIO input pin on the RP2040. The RP2040 utilizes two PIO state machines, one for preamble detection and one for manchester decoding of the message body, to decode the ADS-Bee message. This offers significant cost and power savings over FPGA-based solutions that solve the same problem.

A filtered PWM output from the RP2040 can be used to adjust the bias of the data slicer comparator circuit on the output of the receive signal chain, allowing logarithmic adjustments in receiver sensitivity which can be used to filter out weaker ADS-B signals in congested environments or maximize sensitivity for increased receive range.

Message decoding and aircraft dictionary maintenance is conducted on the RP2040, which works as a SPI "master". An ESP32 S3 functioning as a SPI "slave" ingests raw packets from the RP2040 and maintains a separate, identical, aircraft dictionary for use in reporting over network interfaces (WiFi, perhaps Ethernet in the future).