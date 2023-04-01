# ADS-Bee

The ADS-Bee is a low-cost open-source radio receiver and decoder for ADS-B packets transmitted by aircraf based on an RP2040 microcontroller.

## General Architecture
The ADS-Bee utilizes some basic RF hardware (SAW filters, LNA, cheap logarithmic power detector) to amplify the received pulse-position-modulated ADS-B waveform into a pulse train that is conditioned by a comparator and fed to a PIO input pin on the RP2040. The RP2040 utilizes two PIO state machines, one for preamble detection and one for manchester decoding of the message body, to decode the ADS-Bee message. This offers significant cost and power savings over FPGA-based solutions that solve the same problem.

A filtered PWM output from the RP2040 can be used to adjust the DC bias of the RF power detector's output, allowing logarithmic adjustments in receiver sensitivity which can be used to filter out weaker ADS-B signals in congested environments or maximize sensitivity for increased receive range.

## Known Flaws
* Current receive pipeline relies on a new packet arriving to push out the old packet, since the PIO peripheral's message_decoder state machine gets stuck waiting for another edge before it can make a decision about whether to flush the previous packet and jump back into the beginning wait_for_decode state. This results in the ADS-Bee always being one packet "behind" what it last received. Theoretically if an aircraft transmitted just one packet and no other aircraft ever transmitted a packet afterwards, you would never receive a decoded packet.
* CRC implementation is probably hella slow and may reduce maximum packet consumption rate.