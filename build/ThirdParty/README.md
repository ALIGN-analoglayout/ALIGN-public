# Running magic
To run the version created from source. (Works on a Linux box.)
````
docker run -it --env="DISPLAY" --env="QT_X11_NO_MITSHM=1" --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" magicfromsource bash
````
