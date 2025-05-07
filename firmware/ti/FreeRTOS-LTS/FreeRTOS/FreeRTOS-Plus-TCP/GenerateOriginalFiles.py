#!/usr/bin/env python3

# Prerequisits: Python 3.7 or greater.
#
# To run this script, go to the root of the FreeRTOS+TCP directory; that is the
# directory in which this script is present. And then invoke it with:
# `python3 your/path/to/GenerateOriginalFiles.py`
#
# After running this script, you will have 9 source files in the root directory
# and two additional folders namely `include` and `portable``.


# Import the shutil library to aid in copying of files and folders to different
# location.
import os
import shutil
import sys

# FreeRTOS Kernel includes. DO NOT change the order in the list.
FreeRTOS_Kernel_Includes = [ 'FreeRTOS.h',
                             'task.h',
                             'queue.h',
                             'semphr.h',
                             'list.h',
                             'event_groups.h',
                             'timers.h' ]

# FreeRTOS+TCP include files. DO NOT change the order in the list.
FreeRTOS_TCP_Includes = [ 'FreeRTOS_IP.h',
                          'FreeRTOSIPConfigDefaults.h',
                          'FreeRTOS_IP_Private.h',
                          'FreeRTOS_IP_Utils.h',
                          'FreeRTOS_IP_Timers.h',
                          'FreeRTOS_ARP.h',
                          'FreeRTOS_DHCP.h',
                          'FreeRTOS_DNS.h',
                          'FreeRTOS_DNS_Cache.h',
                          'FreeRTOS_DNS_Callback.h',
                          'FreeRTOS_DNS_Globals.h',
                          'FreeRTOS_DNS_Networking.h',
                          'FreeRTOS_DNS_Parser.h',
                          'FreeRTOS_ICMP.h',
                          'FreeRTOS_Sockets.h',
                          'FreeRTOS_Stream_Buffer.h',
                          'FreeRTOS_TCP_IP.h',
                          'FreeRTOS_TCP_Reception.h',
                          'FreeRTOS_TCP_State_Handling.h',
                          'FreeRTOS_TCP_Transmission.h',
                          'FreeRTOS_TCP_Utils.h',
                          'FreeRTOS_TCP_WIN.h',
                          'FreeRTOS_UDP_IP.h',
                          'FreeRTOS_errno_TCP.h',
                          'IPTraceMacroDefaults.h',
                          'NetworkInterface.h',
                          'NetworkBufferManagement.h' ]

# A dictionary to hold the modules to combine and the destination.
MODULES_DICT = dict()

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_ARP.c
ARP_modules_to_combine = [ 'source/FreeRTOS_ARP.c' ]

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_DHCP.c
DHCP_modules_to_combine = [ 'source/FreeRTOS_DHCP.c' ]

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_DNS.c
DNS_modules_to_combine = [ 'source/FreeRTOS_DNS.c',
                           'source/FreeRTOS_DNS_Cache.c',
                           'source/FreeRTOS_DNS_Callback.c',
                           'source/FreeRTOS_DNS_Networking.c',
                           'source/FreeRTOS_DNS_Parser.c' ]

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_IP.c
IP_modules_to_combine = [ 'source/FreeRTOS_ICMP.c',
                          'source/FreeRTOS_IP.c',
                          'source/FreeRTOS_IP_Timers.c',
                          'source/FreeRTOS_IP_Utils.c' ]

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_Sockets.c
Socket_modules_to_combine = [ 'source/FreeRTOS_Sockets.c' ]

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_Stream_Buffer.c
StreamBuffer_modules_to_combine = [ 'source/FreeRTOS_Stream_Buffer.c' ]

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_TCP_IP.c
TCP_modules_to_combine = [ 'source/FreeRTOS_TCP_IP.c',
                           'source/FreeRTOS_TCP_Reception.c',
                           'source/FreeRTOS_TCP_State_Handling.c',
                           'source/FreeRTOS_TCP_Transmission.c',
                           'source/FreeRTOS_TCP_Utils.c' ]

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_TCP_WIN.c
TCP_WIN_modules_to_combine = [ 'source/FreeRTOS_TCP_WIN.c',
                               'source/FreeRTOS_Tiny_TCP.c' ]

# DO NOT MODIFY. The modules to combine to make up the original FreeRTOS_UDP_IP.c
UDP_modules_to_combine = [ 'source/FreeRTOS_UDP_IP.c' ]

# Add all the modules and the destinations to the dictionary.
MODULES_DICT['FreeRTOS_ARP.c'] = ARP_modules_to_combine
MODULES_DICT['FreeRTOS_DHCP.c'] = DHCP_modules_to_combine
MODULES_DICT['FreeRTOS_DNS.c'] = DNS_modules_to_combine
MODULES_DICT['FreeRTOS_IP.c'] = IP_modules_to_combine
MODULES_DICT['FreeRTOS_Sockets.c'] = Socket_modules_to_combine
MODULES_DICT['FreeRTOS_Stream_Buffer.c'] = StreamBuffer_modules_to_combine
MODULES_DICT['FreeRTOS_TCP_IP.c'] = TCP_modules_to_combine
MODULES_DICT['FreeRTOS_TCP_WIN.c'] = TCP_WIN_modules_to_combine
MODULES_DICT['FreeRTOS_UDP_IP.c'] = UDP_modules_to_combine

# Sorting function used to add Kernel includes. This is required as the includes
# need to adhere to a specific order of inclusion.
def KernelSortingFunction(element):
    return FreeRTOS_Kernel_Includes.index(element)

# Sorting function used to add FreeRTOS+TCP includes. This is required as the includes
# need to adhere to a specific order of inclusion.
def TCPSortingFunction(element):
    return FreeRTOS_TCP_Includes.index(element)

# Get all the includes in all the modules to combine first. This function does
# remove the duplicates but does not sort the includes in any specific order.
def GetIncludeList(ModulesToCombine):
    # This list is used for the FreeRTOS+TCP include files.
    TCP_include_list = list()
    # This list is used for FreeRTOS Kernel include files.
    Kernel_include_list = list()
    # This list is used for standard library include files.
    StdLib_include_list = list()

    for filename in ModulesToCombine:
        f = open(filename, "r")
        for line in f.readlines():
            if line.lstrip().startswith('#include '):
                if '<' in line:
                    #if this is a standard library include
                    start_token = '<'
                    end_token = '>'
                    header = line.split(start_token)[1].split(end_token)[0]
                    StdLib_include_list.append(header)
                else:
                    start_token = '"'
                    end_token = '"'
                    header = line.split(start_token)[1]

                    if header in FreeRTOS_TCP_Includes:
                        TCP_include_list.append(header)
                    elif header in FreeRTOS_Kernel_Includes:
                        Kernel_include_list.append(header)
                    else:
                        print("ERROR: Found " + header + " which is not in any list!")
        f.close()
    return list(set(StdLib_include_list)), list(set(Kernel_include_list)), list(set(TCP_include_list))

# Write the includes in a specific order to the destination file.
def AddIncludesInFile(modules_to_combine, file_descriptor):
    StdLib_include_list_unique, Kernel_include_list_unique, TCP_include_list_unique = GetIncludeList(modules_to_combine)

    for include in StdLib_include_list_unique:
        file_descriptor.write(f'#include <{include}>\n')

    # Sort the Kernel includes in a specific order using KernelSortingFunction.
    Kernel_include_list_unique.sort(key=KernelSortingFunction)
    for include in Kernel_include_list_unique:
        file_descriptor.write(f'#include "{include}"\n')

    # Sort the TCP includes in a specific order using TCPSortingFunction.
    TCP_include_list_unique.sort(key=TCPSortingFunction)
    for include in TCP_include_list_unique:
        file_descriptor.write(f'#include "{include}"\n')

# Function to add the copyright notice to the destination file.
def AddCopyRightNotice(CopyRightNotice, file_descriptor):
    for line in CopyRightNotice:
        file_descriptor.write(f'{line}')

# Function to generate the original modules by adding the copyright notice,
# includes and source to the destination modules.
def GenerateOriginalModules():
    # Flag to note the first iteration.
    FirstIteration = True
    # Create a list to hold the multi-line copyright notice.
    CopyRightNotice = list()

    for module in MODULES_DICT:
        # Store the copyright notice for future use.
        if FirstIteration:
            FirstIteration = False
            # Open the first module. All modules have copyright notices in them.
            with open(MODULES_DICT[module][0]) as f:
                for line in f.readlines():
                    CopyRightNotice.append(line)

                    if '*/' in line:
                        # Found the end of commented copyright notice. Break out
                        # of the loop.
                        break
                f.close()

        # Combine modules only if they were split into multiple ones.
        if len(MODULES_DICT[module]) != 1:
            with open(module, 'w') as file_to_write:
                # Add the copyright notice to the destination module.
                AddCopyRightNotice(CopyRightNotice, file_to_write)

                # Add the include files in the destination module.
                AddIncludesInFile(MODULES_DICT[module], file_to_write)

                # Add the source from all the modules into the destination
                # module.
                for filename in MODULES_DICT[module]:
                    ready_to_write = False
                    with open(filename, "r") as f:
                        for line in f.readlines():
                            if ready_to_write:
                                file_to_write.write(f'{line}')
                            elif not line.lstrip().startswith('#include') and not line.lstrip().startswith(('*', '/*', '*/')):
                                file_to_write.write(f'{line}')
                                ready_to_write = True
                        f.close()
                file_to_write.close()
        # Some modules are intact and there is no need to combine.
        # Just copy them to the root directory.
        else:
            shutil.copy2(MODULES_DICT[module][0] ,module)

# Function to copy the portable and include directories into the root of the
# folder.
def CopyIncludeAndPortableDirs():
    # Copy the include directory to the root of the folder.
    shutil.copytree('source/include', 'include')
    # Copy the portable directory to the root of the folder.
    shutil.copytree('source/portable', 'portable')

if __name__ == "__main__":
    # Change the working directory to the root of repository.
    os.chdir(os.path.dirname(sys.argv[0]))

    GenerateOriginalModules()
    CopyIncludeAndPortableDirs()
