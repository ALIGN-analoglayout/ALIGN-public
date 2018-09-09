# foo
This is a test repository of the ALIGN-analoglayout repository.

# Run a test using docker

First build the g++ environment including googletest and a json parser:
````bash
docker build -f Dockerfile.build -t with_protobuf .
````
Then build the tester:
````bash
docker build -f Dockerfile.test -t tester .
````
and finally execute the tests:
````bash
docker run --rm -t tester /Apps/src/tester
docker run --rm -t tester /Apps/src/ptest
````


