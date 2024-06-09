# ADSBee 1090

ADSBee 1090 is an open-source radio receiver and decoder for ADS-B packets transmitted by aircraft on 1090MHz. ADSBee 1090 is based on an RP2040 microcontroller, and utilizes two independent PIO blocks to find and decode ADS-B messages without the need for an FPGA. ADSBee 1090 includes a radio receiver frontend with filtering and amplification, as well as a software defined comparator circuit with adjustable gain and trigger thresholds for customizable receive sensitivity in a diverse range of RF environments.

![ADSBee 1090 Logo](affinity/adsbee_logo/exports/adsbee_logo_color.png)

## Features
* Decoding of 1090MHz transponder signals (ADS-B and Mode S).
* 1x USB console input / output for changing parameters and transmitting data.
* 1x UART output for transmitting data.
* Built-in EEPROM for storing nonvolatile settings.
* Feature-rich AT command set for customizing baud rates, output data protocols, signal conditioning values, etc.
* Multiple supported output protocols:
    * Raw packets
    * MAVLINK
    * GDL90 (not yet implemented)
    * CSV (not yet implemented)
* 2.4GHz 802.11 radio for automatic streaming of decoded values to custom endpoints on the internet. No external compute required, just add WiFi and power!
* GNSS module connector for MLAT and ground station location information.
* Low(ish) power draw, enabling embedded installations in solar-powered outdoor receivers.

## General Architecture
The ADS-Bee utilizes some basic RF hardware (SAW filters, LNA, logarithmic power detector) to amplify the received pulse-position-modulated ADS-B waveform into a pulse train that is conditioned by a comparator and fed to a PIO input pin on the RP2040. The RP2040 utilizes two PIO state machines, one for preamble detection and one for manchester decoding of the message body, to decode the ADS-Bee message. This offers significant cost and power savings over FPGA-based solutions that solve the same problem, at the cost of lower performance in noisy environments where an FPGA-based correlation approach offers improved noise immunity.

A filtered PWM output from the RP2040 can be used to adjust the bias of both the up-going and down-going trigger thresholds that define the comparator's hysteresis, allowing logarithmic adjustments in receiver sensitivity which can be used to filter out weaker ADS-B signals in congested environments or maximize sensitivity for increased receive range. An analog gain stage between the RF detector output and the RF comparator allows software-defined adjustable gain values between 1x and 101x via the use of a digital potentiometer, allowing further flexibility in tuning receiver sensitivity.