# ALIGN
This is a test repository of the ALIGN-analoglayout repository.

# Run a test using docker

First build the g++ environment including googletest, a json parser, and protobuf:
````bash
docker build -f Dockerfile.build -t with_protobuf .
````
Then build the tester:
````bash
docker build -f Dockerfile.test -t tester .
````
and finally execute the tests:
````bash
docker run --rm -t tester /Apps/src/json/tester
docker run --rm -t tester /Apps/src/proto/ptest
````

This was tried using Ubuntu 18.04 using the docker installation instructions found here: https://docs.docker.com/install/linux/docker-ce/ubuntu/

# Modification when behind the firewall at Intel

The docker build commands need the following arguments:
````bash
--build-arg http_proxy=http://proxy-chain.intel.com:911 --build-arg https_proxy=http://proxy-chain.intel.com:911
````
so the build commands become:
````bash
docker build -f Dockerfile.build -t with_protobuf --build-arg http_proxy=http://proxy-chain.intel.com:911 --build-arg https_proxy=http://proxy-chain.intel.com:911 .
docker build -f Dockerfile.test -t tester --build-arg http_proxy=http://proxy-chain.intel.com:911 --build-arg https_proxy=http://proxy-chain.intel.com:911 .
````
Also, it seems that the http_proxy and https_proxy environment variables should not be set in the shell where you execute these docker build commands.

This was tried using WSL (Windows Subsystem for Linux) on a Win 10 Pro machine. The docker daemon is running as a windows process. The docker build and run command are executed in a WSL Ubuntu 18.04 shell.
