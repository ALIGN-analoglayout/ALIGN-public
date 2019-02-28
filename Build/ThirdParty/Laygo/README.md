# Build Laygo

````
docker build -t laygo .
````

# Run first example

````
docker run --mount source=laygoVol,target=/OUTPUT -it laygo bash -c "source /sympy/bin/activate && cd /laygo && PYTHONPATH=/:. python quick_start_GDS.py && cp *.gds /OUTPUT"
````

then run the GDS viewer:

````
docker run --env="DISPLAY" --env="QT_X11_NO_MITSHM=1" --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" --mount source=laygoVol,target=/OUTPUT darpaalign/klayout bash -c klayout
````