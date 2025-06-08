################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
SYSCFG_SRCS += \
../rfPacketRx.syscfg 

LDS_SRCS += \
../cc13x2_cc26x2_nortos.lds 

C_SRCS += \
../RFQueue.c \
../main_nortos.c \
../rfPacketRx.c \
./syscfg/ti_devices_config.c \
./syscfg/ti_radio_config.c \
./syscfg/ti_drivers_config.c 

GEN_FILES += \
./syscfg/ti_devices_config.c \
./syscfg/ti_radio_config.c \
./syscfg/ti_drivers_config.c \
./syscfg/ti_utils_build_compiler.opt 

GEN_MISC_DIRS += \
./syscfg 

C_DEPS += \
./RFQueue.d \
./main_nortos.d \
./rfPacketRx.d \
./syscfg/ti_devices_config.d \
./syscfg/ti_radio_config.d \
./syscfg/ti_drivers_config.d 

GEN_OPTS += \
./syscfg/ti_utils_build_compiler.opt 

OBJS += \
./RFQueue.o \
./main_nortos.o \
./rfPacketRx.o \
./syscfg/ti_devices_config.o \
./syscfg/ti_radio_config.o \
./syscfg/ti_drivers_config.o 

GEN_MISC_FILES += \
./syscfg/ti_radio_config.h \
./syscfg/ti_drivers_config.h \
./syscfg/ti_utils_build_linker.cmd.genlibs \
./syscfg/ti_utils_build_linker.cmd.genmap \
./syscfg/syscfg_c.rov.xs 

GEN_MISC_DIRS__QUOTED += \
"syscfg" 

OBJS__QUOTED += \
"RFQueue.o" \
"main_nortos.o" \
"rfPacketRx.o" \
"syscfg/ti_devices_config.o" \
"syscfg/ti_radio_config.o" \
"syscfg/ti_drivers_config.o" 

GEN_MISC_FILES__QUOTED += \
"syscfg/ti_radio_config.h" \
"syscfg/ti_drivers_config.h" \
"syscfg/ti_utils_build_linker.cmd.genlibs" \
"syscfg/ti_utils_build_linker.cmd.genmap" \
"syscfg/syscfg_c.rov.xs" 

C_DEPS__QUOTED += \
"RFQueue.d" \
"main_nortos.d" \
"rfPacketRx.d" \
"syscfg/ti_devices_config.d" \
"syscfg/ti_radio_config.d" \
"syscfg/ti_drivers_config.d" 

GEN_FILES__QUOTED += \
"syscfg/ti_devices_config.c" \
"syscfg/ti_radio_config.c" \
"syscfg/ti_drivers_config.c" \
"syscfg/ti_utils_build_compiler.opt" 

C_SRCS__QUOTED += \
"../RFQueue.c" \
"../main_nortos.c" \
"../rfPacketRx.c" \
"./syscfg/ti_devices_config.c" \
"./syscfg/ti_radio_config.c" \
"./syscfg/ti_drivers_config.c" 

SYSCFG_SRCS__QUOTED += \
"../rfPacketRx.syscfg" 


