# ClusterFuzzLite set up

This folder contains a fuzzing set for [ClusterFuzzLite](https://google.github.io/clusterfuzzlite).


## Running the fuzzer locally

To reproduce the fuzzing by way of [OSS-Fuzz](https://github.com/google/oss-fuzz) (which ClusterFuzzLite will be using):

```sh
git clone https://github.com/google/oss-fuzz

# Notice the destination folder shuold be in lower case.
git clone https://github.com/FreeRTOS/coreJSON corejson
cd corejson

# Build the fuzzers in .clusterfuzzlite
python3 ../oss-fuzz/infra/helper.py build_fuzzers --external $PWD

# Run the fuzzer for 180 seconds
python3 ../oss-fuzz/infra/helper.py run_fuzzer --external $PWD validate_fuzzer -- -max_total_time=180
```
