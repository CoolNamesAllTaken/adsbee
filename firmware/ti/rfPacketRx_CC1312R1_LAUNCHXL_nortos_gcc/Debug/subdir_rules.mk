################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Each subdirectory must supply rules for building sources it contributes
%.o: ../%.c $(GEN_OPTS) | $(GEN_FILES) $(GEN_MISC_FILES)
	@echo 'Building file: "$<"'
	@echo 'Invoking: GNU Compiler'
	"/Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi/bin/arm-none-eabi-gcc-14.2.1" -c -mcpu=cortex-m4 -march=armv7e-m -mthumb -mfloat-abi=hard -mfpu=fpv4-sp-d16 -I"/Users/jmcnelly/git-checkouts/adsbee/firmware/ti/rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc" -I"/Users/jmcnelly/git-checkouts/adsbee/firmware/ti/rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc/Debug" -I"/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/source" -I"/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/kernel/nortos" -I"/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/kernel/nortos/posix" -I"/Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi/arm-none-eabi/include/newlib-nano" -I"/Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi/arm-none-eabi/include" -ffunction-sections -fdata-sections -g -gdwarf-3 -gstrict-dwarf -Wall -MMD -MP -MF"$(basename $(<F)).d_raw" -MT"$(@)" -I"/Users/jmcnelly/git-checkouts/adsbee/firmware/ti/rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc/Debug/syscfg" -std=c99 $(GEN_OPTS__FLAG) -o"$@" "$<"
	@echo 'Finished building: "$<"'
	@echo ' '

build-1016284431: ../rfPacketRx.syscfg
	@echo 'Building file: "$<"'
	@echo 'Invoking: SysConfig'
	"/Users/jmcnelly/ti/sysconfig_1.21.1/sysconfig_cli.sh" --script "/Users/jmcnelly/git-checkouts/adsbee/firmware/ti/rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc/rfPacketRx.syscfg" -o "syscfg" -s "/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/.metadata/product.json" --compiler gcc
	@echo 'Finished building: "$<"'
	@echo ' '

syscfg/ti_devices_config.c: build-1016284431 ../rfPacketRx.syscfg
syscfg/ti_radio_config.c: build-1016284431
syscfg/ti_radio_config.h: build-1016284431
syscfg/ti_drivers_config.c: build-1016284431
syscfg/ti_drivers_config.h: build-1016284431
syscfg/ti_utils_build_linker.cmd.genlibs: build-1016284431
syscfg/ti_utils_build_linker.cmd.genmap: build-1016284431
syscfg/ti_utils_build_compiler.opt: build-1016284431
syscfg/syscfg_c.rov.xs: build-1016284431
syscfg: build-1016284431

syscfg/%.o: ./syscfg/%.c $(GEN_OPTS) | $(GEN_FILES) $(GEN_MISC_FILES)
	@echo 'Building file: "$<"'
	@echo 'Invoking: GNU Compiler'
	"/Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi/bin/arm-none-eabi-gcc-14.2.1" -c -mcpu=cortex-m4 -march=armv7e-m -mthumb -mfloat-abi=hard -mfpu=fpv4-sp-d16 -I"/Users/jmcnelly/git-checkouts/adsbee/firmware/ti/rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc" -I"/Users/jmcnelly/git-checkouts/adsbee/firmware/ti/rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc/Debug" -I"/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/source" -I"/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/kernel/nortos" -I"/Users/jmcnelly/ti/simplelink_cc13xx_cc26xx_sdk_8_30_01_01/kernel/nortos/posix" -I"/Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi/arm-none-eabi/include/newlib-nano" -I"/Applications/ArmGNUToolchain/14.2.rel1/arm-none-eabi/arm-none-eabi/include" -ffunction-sections -fdata-sections -g -gdwarf-3 -gstrict-dwarf -Wall -MMD -MP -MF"syscfg/$(basename $(<F)).d_raw" -MT"$(@)" -I"/Users/jmcnelly/git-checkouts/adsbee/firmware/ti/rfPacketRx_CC1312R1_LAUNCHXL_nortos_gcc/Debug/syscfg" -std=c99 $(GEN_OPTS__FLAG) -o"$@" "$<"
	@echo 'Finished building: "$<"'
	@echo ' '


