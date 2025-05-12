# This imports.mak is used to override the default imports.mak at the root of the ti_lowpoer_lpf2_sdk module during a Dockerfile build.

XDC_INSTALL_DIR        ?= /home/username/ti/xdctools_3_62_01_15_core
SYSCONFIG_TOOL         ?= /home/username/ti/ccs1270/ccs/utils/sysconfig_1.21.1/sysconfig_cli.sh

CMAKE                  ?= $ENV{CMAKE}
PYTHON                 ?= $ENV{PYTHON}

# TICLANG_ARMCOMPILER    ?= /home/username/ti/ccs1270/ccs/tools/compiler/ti-cgt-armllvm_3.2.2.LTS-0
GCC_ARMCOMPILER        ?= $ENV{GCC_ARMCOMPILER}
# IAR_ARMCOMPILER        ?= /home/username/iar9.50.2

# Uncomment this to enable the TFM build
# ENABLE_TFM_BUILD=1

ifeq ("$(SHELL)","sh.exe")
# for Windows/DOS shell
    RM      = del
    RMDIR   = -rmdir /S /Q
    DEVNULL = NUL
    ECHOBLANKLINE = @cmd /c echo.
else
# for Linux-like shells
    RM      = rm -f
    RMDIR   = rm -rf
    DEVNULL = /dev/null
    ECHOBLANKLINE = echo
endif
