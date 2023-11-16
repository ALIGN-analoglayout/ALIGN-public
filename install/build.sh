#!/bin/sh
docker build --build-arg UID=$(id -u) --build-arg GID=$(id -g) -t align_local_$(whoami) .
