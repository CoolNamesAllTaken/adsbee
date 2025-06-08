# Static code analysis for FreeRTOS-Plus-TCP library
This directory is made for the purpose of statically testing the MISRA C:2012 compliance of FreeRTOS+TCP using
[Synopsys Coverity](https://www.synopsys.com/software-integrity/security-testing/static-analysis-sast.html) static analysis tool.
To that end, this directory provides a [CMake](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/test/Coverity/CMakeLists.txt)
file and [configuration files](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/tree/main/test/Coverity/ConfigFiles) required to build
an application for the tool to analyze.

> **Note**
For generating the report as outlined below, we have used Coverity version 2018.09.

For details regarding the suppressed violations in the report (which can be generated using the instructions described below), please
see the [MISRA.md](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md) file.

## Getting Started
### Prerequisites
You can run this on a platform supported by Coverity. The list and other details can be found [here](https://sig-docs.synopsys.com/polaris/topics/c_coverity-compatible-platforms.html).
To compile and run the Coverity target successfully, you must have the following:

1. CMake version > 3.13.0 (You can check whether you have this by typing `cmake --version`)
2. GCC compiler
    - You can see the downloading and installation instructions [here](https://gcc.gnu.org/install/).
3. Download the repo and include the submodules using the following commands.
    - `git clone --recurse-submodules https://github.com/FreeRTOS/FreeRTOS-Plus-TCP.git ./FreeRTOS_TCP`
    - `cd ./FreeRTOS_TCP`
    - `git submodule update --checkout --init --recursive`

### To build and run coverity:
Go to the root directory of the FreeRTOS-Plus-TCP repo and run the following commands in terminal:
1. Update the compiler configuration in Coverity
  ~~~
  cov-configure --force --compiler cc --comptype gcc
  ~~~
2. Create the build files using CMake in a `build` directory
  ~~~
  cmake -B build -S test/Coverity
  ~~~
3. Go to the build directory and copy the coverity configuration file
  ~~~
  cd build/
  cp ../test/Coverity/coverity_misra.config .
  ~~~
4. Build the (pseudo) application
  ~~~
  cov-build --emit-complementary-info --dir cov-out make
  ~~~
5. Go to the Coverity output directory (`cov-out`) and begin Coverity static analysis
  ~~~
  cd cov-out/
  cov-analyze --dir . --coding-standard-config ../coverity_misra.config --tu-pattern "file('.*/FreeRTOS-Plus-TCP/source/.*')"
  ~~~
6. Format the errors in HTML format so that it is more readable while removing the FreeRTOS-Kernel directory from the report
  ~~~
  cov-format-errors --dir . --exclude-files '(.*/FreeRTOS-Kernel/.*)' --html-output html-output
  ~~~

You should now have the HTML formatted violations list in a directory named `html-output`.
With the current configuration and the provided project, you should see only one deviation from advisory rule 8.13 in file
FreeRTOS_IP.c [here](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/4ac10c84a384f0414f4aec0d4be0ee7c345f2f8b/source/FreeRTOS_IP.c#L236).
This deviation has a justification outlined [here](https://github.com/FreeRTOS/FreeRTOS-Plus-TCP/blob/main/MISRA.md#rule-813). With
that justification in place, a coverity suppression statement has been added to the code. However, even with that suppression in
place, the coverity tool continues to report the deviation. Thus, as an exception, we have allowed the deviation to be reported in
the HTML formatted report. If you find a way around it, please help us fix this by creating a pull-request in this repository.
