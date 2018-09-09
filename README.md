# foo
This is a test repository of the ALIGN-analoglayout repository.

# Run a test using docker

First build the g++ environment including googletest and a json parser:
````bash
docker build -f Dockerfile.c -t stevenmburns/with_json .
````
Then build the tester:
````bash
docker build -f Dockerfile.test -t stevenmburns/tester .
````
and finally execute the test:
````bash
docker run --rm -t stevenmburns/tester
````


