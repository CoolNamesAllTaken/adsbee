################################################################################
# Automatically-generated file. Do not edit!
################################################################################

CG_TOOL_ROOT := /Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi

GEN_OPTS__FLAG := @"syscfg/ti_utils_build_compiler.opt" 
GEN_CMDS__FLAG := 

ORDERED_OBJS += \
"./RFQueue.o" \
"./main_nortos.o" \
"./rfPacketRx.o" \
"./syscfg/ti_devices_config.o" \
"./syscfg/ti_radio_config.o" \
"./syscfg/ti_drivers_config.o" \
-Wl,-T"../cc13x2_cc26x2_nortos.lds" \
$(GEN_CMDS__FLAG) \
-l:ti_utils_build_linker.cmd.genlibs \
-lgcc \
-lc \
-lm \

-include ../makefile.init

RM := rm -rf
RMDIR := rm -rf

# All of the sources participating in the build are defined here
-include sources.mk
-include subdir_vars.mk
-include subdir_rules.mk
-include objects.mk

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(strip $(C55_DEPS)),)
-include $(C55_DEPS)
endif
ifneq ($(strip $(C_UPPER_DEPS)),)
-include $(C_UPPER_DEPS)
endif
ifneq ($(strip $(S67_DEPS)),)
-include $(S67_DEPS)
endif
ifneq ($(strip $(S62_DEPS)),)
-include $(S62_DEPS)
endif
ifneq ($(strip $(S_DEPS)),)
-include $(S_DEPS)
endif
ifneq ($(strip $(OPT_DEPS)),)
-include $(OPT_DEPS)
endif
ifneq ($(strip $(C??_DEPS)),)
-include $(C??_DEPS)
endif
ifneq ($(strip $(ASM_UPPER_DEPS)),)
-include $(ASM_UPPER_DEPS)
endif
ifneq ($(strip $(S??_DEPS)),)
-include $(S??_DEPS)
endif
ifneq ($(strip $(C64_DEPS)),)
-include $(C64_DEPS)
endif
ifneq ($(strip $(CXX_DEPS)),)
-include $(CXX_DEPS)
endif
ifneq ($(strip $(S64_DEPS)),)
-include $(S64_DEPS)
endif
ifneq ($(strip $(INO_DEPS)),)
-include $(INO_DEPS)
endif
ifneq ($(strip $(CLA_DEPS)),)
-include $(CLA_DEPS)
endif
ifneq ($(strip $(S55_DEPS)),)
-include $(S55_DEPS)
endif
ifneq ($(strip $(SV7A_DEPS)),)
-include $(SV7A_DEPS)
endif
ifneq ($(strip $(C62_DEPS)),)
-include $(C62_DEPS)
endif
ifneq ($(strip $(C67_DEPS)),)
-include $(C67_DEPS)
endif
ifneq ($(strip $(PDE_DEPS)),)
-include $(PDE_DEPS)
endif
ifneq ($(strip $(K_DEPS)),)
-include $(K_DEPS)
endif
ifneq ($(strip $(C_DEPS)),)
-include $(C_DEPS)
endif
ifneq ($(strip $(CC_DEPS)),)
-include $(CC_DEPS)
endif
ifneq ($(strip $(C++_DEPS)),)
-include $(C++_DEPS)
endif
ifneq ($(strip $(C43_DEPS)),)
-include $(C43_DEPS)
endif
ifneq ($(strip $(S43_DEPS)),)
-include $(S43_DEPS)
endif
ifneq ($(strip $(ASM_DEPS)),)
-include $(ASM_DEPS)
endif
ifneq ($(strip $(S_UPPER_DEPS)),)
-include $(S_UPPER_DEPS)
endif
ifneq ($(strip $(CPP_DEPS)),)
-include $(CPP_DEPS)
endif
ifneq ($(strip $(SA_DEPS)),)
-include $(SA_DEPS)
endif
endif

-include ../makefile.defs

# Add inputs and outputs from these tool invocations to the build variables 
EXE_OUTPUTS += \
rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc.out 

EXE_OUTPUTS__QUOTED += \
"rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc.out" 


# All Target
all: $(OBJS) $(LDS_SRCS) $(GEN_CMDS)
	@$(MAKE) --no-print-directory -Onone "rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc.out"

# Tool invocations
rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc.out: $(OBJS) $(LDS_SRCS) $(GEN_CMDS)
	@echo 'Building target: "$@"'
	@echo 'Invoking: GNU Linker'
	"/Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi/bin/arm-none-eabi-gcc-14.2.1" -mfpu=fpv4-sp-d16 -ffunction-sections -fdata-sections -g -gdwarf-3 -gstrict-dwarf -Wall -mcpu=cortex-m4 -Wl,-Map,"rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc.map" --entry resetISR -nostartfiles -static -Wl,--gc-sections -L"/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/source" -L"/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/kernel/nortos" -L"/Users/jmcnelly/git-checkouts/adsbee/firmware/ti/rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc/Debug/syscfg" -L"/Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi/arm-none-eabi/lib/thumb/v7e-m/hard" -march=armv7e-m -mthumb -mfloat-abi=hard -mfpu=fpv4-sp-d16 --specs=nano.specs --specs=nosys.specs -o"rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc.out" $(ORDERED_OBJS)
	@echo 'Finished building target: "$@"'
	@echo ' '

# Other Targets
clean:
	-$(RM) $(GEN_MISC_FILES__QUOTED)$(GEN_FILES__QUOTED)$(EXE_OUTPUTS__QUOTED)
	-$(RM) "RFQueue.o" "main_nortos.o" "rfPacketRx.o" "syscfg/ti_devices_config.o" "syscfg/ti_radio_config.o" "syscfg/ti_drivers_config.o" 
	-$(RM) "RFQueue.d" "main_nortos.d" "rfPacketRx.d" "syscfg/ti_devices_config.d" "syscfg/ti_radio_config.d" "syscfg/ti_drivers_config.d" 
	-$(RMDIR) $(GEN_MISC_DIRS__QUOTED)
	-@echo 'Finished clean'
	-@echo ' '

.PHONY: all clean dependents
.SECONDARY:

-include ../makefile.targets

