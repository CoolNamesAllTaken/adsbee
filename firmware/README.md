# ads-bee

## Docker Setup Instructions

Run these commands from the top level directory.

NOTE: Cloning git repos onto windows may result in files with CR+LF line endings. Docker does NOT like these, and they will break everything. Make sure that you set `git config --global core.autocrlf false` before cloning repos that will get added or mounted to a Docker container.

### Build the Docker Image

Be sure to run `git submodule update --init` before building!

From this directory, run the following shell command.

```bash
docker build -t pico-dev-image .
```

### Run the Docker Container

Starting an interactive docker container on Linux or Mac. Mounts the `firmware` directory to `/root/firmware`.

```bash
docker run --name ads-bee-dev -it --mount type=bind,source="$(pwd)",target=/root/adsbee pico-dev-image
```

Starting an interactive docker container on Windows. Mounts the `firmware` directory to `/root/firmware`.

```bash
winpty docker run --name ads-bee-dev -it --mount type=bind,source="$(pwd)",target=/root/adsbee pico-dev-image
```

### Remove the Docker Image

```bash
docker image rm pico-dev-image
```

## Using VS Code inside the Docker Container

1. Install the Docker VS Code extension.
2. Right click on the available pico-dev-container and select "Attach Visual Studio Code" from the dropdown menu.
3. Open the attached VS Code, and wait for it to finish installing docker stuff.
4. In the attached visual studio code, install Cortex-Debug and the C/C++ extension.
5. To debug using the `launch.json` file in the `firmware/.vscode` directory, use the "Open Folder" function to navigate the attached VS Code instance to the `firmware` directory.

## Building Tests

### Build GoogleTest
In the docker container, navigate to the `modules/googletest` folder and execute the following.

```bash
cd googletest        # Main directory of the cloned repository.
mkdir build          # Create a directory to hold the build output.
cd build
cmake -DBUILD_SHARED_LIBS=ON .. # Generate build scripts with .so files.
make
```

This will generate the libgtest.so file that is a dependency of the ads-bee tests in the next section.

### Build ads-bee Tests
Create a folder called `test/build` and open a terminal there.
```bash
cmake ..
make
./adsbee_test
```

## Initializing Submodules

From the `modules` directory, run `git submodule update --init --recursive`.

Build googletest:
```bash
cd /adsbee/modules/googletest
mkdir build
cd build
cmake cmake -DBUILD_SHARED_LIBS=ON ..
make
```