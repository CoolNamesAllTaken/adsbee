## Disclaimer :

Please note that MSP432 port has not been tested with IPv6, Multiple endpoint and interfaces which are supported by the latest TCP release V4.0.0. This needs to be used with caution in IPv6 environment as there can be potential compatibility issues.

## Last Git Release :

You can find the last release supporting this port on our GitHub repository here : [V3.1.0](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/releases/tag/V3.1.0). Visit the mentioned link to access the repository and download the version supporting MSP432 port to use it.

## Contribution and Support :

If you are interested in contributing to the development of this port or have any question regarding this port, feel free to post on [FreeRTOS forum](https://forums.freertos.org/). Your inputs are valuable to us and we encourage collaboration and discussion within the community.

# Scope
This is a driver and network middleware for the MSP432E401Y microcontroller
with built-in Ethernet MAC.

# Prerequisites

Ensure that driverlib for the MSP432E4 is installed and added to the include
path for the project.

# Recommendation
When a MAC address changes or when there is a change in the network setup,
it is recommended to perform a hard reset of the microcontroller in lieu
of resetting only the MAC hardware.

# List of Tasks

The tasks listed in the table below are implemented internally by the driver (NetworkInterface.c).

| Task Name                             | Purpose                                                           |
|---------------------------------------|-------------------------------------------------------------------|
| prvEMACDeferredInterruptHandlerTaskRX | RX Task                                                           |
| prvEMACDeferredInterfaceOutputTaskTX  | TX Task                                                           |
| prvCheckLinkUpOrDownNetStateTask      | Network State Checking Task (link up/down, network state & reset) |

The tasks listed in the table below are implemented by additional code provided as an example
related to how the driver might be used in an application (NetworkMiddleware.c).
The additional code does not have to be used and is only provided to be useful.

| Task Name                             | Purpose                                                           |
|---------------------------------------|-------------------------------------------------------------------|
| prvNetworkResetTask                   | Task to periodically reset the network (if required)

# Example Code

```
#include "NetworkInterface.h"
#include "NetworkMiddleware.h"

void setup_wired_ethernet()
{
    struct InternalNetworkInterfaceMSP432EConfig config;
    vGetInternalNetworkInterfaceMSP432EConfigDefaults(&config);
    config.setMACAddrInternal = false;  /* true if the MAC address is to be read from microcontroller flash */
    config.MACAddr[0] = 0x70;           /* replace with a custom MAC address */
    config.MACAddr[1] = 0xFF;
    config.MACAddr[2] = 0x76;
    config.MACAddr[3] = 0x1C;
    config.MACAddr[4] = 0xC1;
    config.MACAddr[5] = 0xD0;
    vPublicSetupEMACNetwork(config);

    /* setup the network stack middleware */
    const char *devname = "device";
    struct InternalNetworkMiddlewareData setupData;
    strncpy(setupData.deviceName, devname, strlen(devname));
    setupData.resetNetworkTaskEveryXSeconds = 86400;           /* Restart the network every 24 hours (86400 seconds) only when  setupData.resetNetworkTaskRunning == true */
    setupData.resetNetworkTaskRunning = false;                /* Run the network task to reset the network every so often (i.e. to periodically obtain a new IP address) */

    /* set the static IP address */
    vConvertOctetsToAddr(setupData.ucIPAddress, 192, 168, 1, 9);
    vConvertOctetsToAddr(setupData.ucNetMask, 255, 255, 255, 0);
    vConvertOctetsToAddr(setupData.ucGatewayAddress, 192, 168, 1, 1);
    vConvertOctetsToAddr(setupData.ucDNSServerAddress, 192, 168, 1, 1);

    vPublicSetupFreeRTOSTasks(setupData);
    /*
       Start the RTOS scheduler by calling vTaskStartScheduler()
       Use publicPreventNetworkReset() to block the network reset during a critical section of the code
       Set the device name using vPublicSetupDeviceName()
    */
}

```
# Contact
Nicholas J. Kinar (n.kinar@usask.ca) or FreeRTOS Forums
