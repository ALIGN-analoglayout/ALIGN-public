# Build
Here are two sample build environments.

# Run a C++-based test using docker

First build the g++ environment including googletest, a json parser, and protobuf:
````bash
docker build -f Dockerfile.build -t with_protobuf .
````
Then copy the src directory to a Docker volume (one time)
````bash
tar cvf - src | docker run --rm --mount source=srcVol,target=/vol -i ubuntu bash -c "cd /vol; tar xvf -"
````
and finally execute the tests:
````bash
docker run --rm --mount source=srcVol,target=/vol -t with_protobuf bash -c "cd /vol/src/json && make && ./tester"
docker run --rm --mount source=srcVol,target=/vol -t with_protobuf bash -c "cd /vol/src/proto && make && ./ptest"
````

This was tried using Ubuntu 18.04 using the docker installation instructions found here: https://docs.docker.com/install/linux/docker-ce/ubuntu/

# Run a Python-based test using docker

The docker build command is:
```bash
docker build -f Dockerfile.build.python -t with_python .
```

To run a python example, try:
```bash
tar cvf - src | docker run --rm --mount source=srcVol,target=/vol -i ubuntu bash -c "cd /vol; tar xvf -"
docker run --rm --mount source=srcVol,target=/vol -t with_python bash -c "source /sympy/bin/activate && cd /vol/src/call-c-from-python  && python setup.py build && python setup.py install && pytest"
````

## C++ Coverage
You can also get a coverage report for C++ code.
Try this:
```bash
tar cvf - src | docker run --rm --mount source=srcVol,target=/vol -i ubuntu bash -c "cd /vol; tar xvf -"

docker run --rm --mount source=srcVol,target=/vol -t with_protobuf bash -c "cd /vol/src/json && make && ./tester && lcov --directory . --capture --output-file ./code_coverage.info -rc lcov_branch_coverage=1 && genhtml code_coverage.info --branch-coverage --output-directory ./code_coverage_report/"

docker run --rm -p 8000:8000 --mount source=srcVol,target=/vol -d with_python bash -c "source /sympy/bin/activate && cd /vol/src/json/code_coverage_report && python -m http.server"
```
Then look at `localhost:8000`.
To make this work we added the compile options:
```
-fprofile-arcs -ftest-coverage
```
to the Makefile in `src/json`.


# Modification when behind the firewall at Intel

The docker build commands need the following additional arguments behind the Intel firewall:
````bash
--build-arg http_proxy=http://proxy-chain.intel.com:911 --build-arg https_proxy=http://proxy-chain.intel.com:911
````
It seems that the http_proxy and https_proxy environment variables should not be set in the shell where you execute these docker build commands.

This was tried using WSL (Windows Subsystem for Linux) on a Win 10 Pro machine. The docker daemon is running as a windows process. The docker build and run command are executed in a WSL Ubuntu 18.04 shell.


