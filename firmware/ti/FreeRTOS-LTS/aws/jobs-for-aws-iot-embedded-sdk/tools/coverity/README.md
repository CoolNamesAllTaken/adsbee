# Static code analysis for Jobs-for-AWS-IoT-embedded-sdk library
This directory is made for the purpose of statically testing the MISRA C:2012 compliance of Jobs-for-AWS-IoT-embedded-sdk using
[Synopsys Coverity](https://www.synopsys.com/software-integrity/security-testing/static-analysis-sast.html) static analysis tool.
To that end, this directory provides a [configuration file](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/blob/main/tools/coverity/misra.config) to use when
building a binary for the tool to analyze.

> **Note**
For generating the report as outlined below, we have used Coverity version 2023.6.1.

For details regarding the suppressed violations in the report (which can be generated using the instructions described below), please
see the [MISRA.md](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/blob/main/MISRA.md) file.

## Getting Started
### Prerequisites
You can run this on a platform supported by Coverity. The list and other details can be found [here](https://sig-docs.synopsys.com/polaris/topics/c_coverity-compatible-platforms.html).
To compile and run the Coverity target successfully, you must have the following:

1. CMake version > 3.13.0 (You can check whether you have this by typing `cmake --version`)
2. GCC compiler
    - You can see the downloading and installation instructions [here](https://gcc.gnu.org/install/).
3. Download the repo and include the submodules using the following commands.
    - `git clone --recurse-submodules git@github.com:aws/Jobs-for-AWS-IoT-embedded-sdk.git ./Jobs-for-AWS-IoT-embedded-sdk`
    - `cd ./Jobs-for-AWS-IoT-embedded-sdk`
    - `git submodule update --checkout --init --recursive`

### To build and run coverity:
Go to the root directory of the library and run the following commands in terminal:
1. Update the compiler configuration in Coverity
  ~~~
  cov-configure --force --compiler cc --comptype gcc
  ~~~
2. Create the build files using CMake in a `build` directory
  ~~~
  cmake -B build -S test -DCOV_ANALYSIS
  ~~~
3. Go to the build directory and copy the coverity configuration file
  ~~~
  cd build/
  ~~~
4. Build the static analysis target
  ~~~
  cov-build --emit-complementary-info --dir cov-out make coverity_analysis
  ~~~
5. Go to the Coverity output directory (`cov-out`) and begin Coverity static analysis
  ~~~
  cd cov-out/
  cov-analyze --dir . --coding-standard-config ../../tools/coverity/misra.config --tu-pattern "file('.*/source/.*')"
  ~~~
6. Format the errors in HTML format so that it is more readable while removing the test and build directory from the report
  ~~~
  cov-format-errors --dir . --file "source" --exclude-files '(/build/|/test/)' --html-output html-out;
  ~~~
7. Format the errors in JSON format to perform a jq query to get a simplified list of any exceptions.
  NOTE: A blank output means there are no defects that aren't being suppressed by the config or inline comments.
  ~~~
  cov-format-errors --dir . --file "source" --exclude-files '(/build/|/test/)' --json-output-v2 defects.json;
  echo -e "\n-------------------------Non-Suppresed Deviations, if any, Listed Below-------------------------\n";
  jq '.issues[] | .events[] | .eventTag ' defects.json | sort | uniq -c | sort -nr;
   echo -e "\n-------------------------Non-Suppresed Deviations, if any, Listed Above-------------------------\n";
  ~~~

For your convenience the commands above are below to be copy/pasted into a UNIX command friendly terminal.
 ~~~
 cov-configure --force --compiler cc --comptype gcc;
 cmake -B build -S test -DCOV_ANALYSIS;
 cd build/;
 cov-build --emit-complementary-info --dir cov-out make coverity_analysis;
 cd cov-out/
 cov-analyze --dir . --coding-standard-config ../../tools/coverity/misra.config;
 cov-format-errors --dir . --file "source" --exclude-files '(/build/|/test/)' --html-output html-out;
 cov-format-errors --dir . --file "source" --exclude-files '(/build/|/test/)' --json-output-v2 defects.json;
 echo -e "\n-------------------------Non-Suppresed Deviations, if any, Listed Below-------------------------\n";
 jq '.issues[] | .events[] | .eventTag ' defects.json | sort | uniq -c | sort -nr;
 echo -e "\n-------------------------Non-Suppresed Deviations, if any, Listed Above-------------------------\n";
 cd ../../;
 ~~~

You should now have the HTML formatted violations list in a directory named `build/cov-out/html-output`.
With the current configuration and the provided project, you should not see any deviations.