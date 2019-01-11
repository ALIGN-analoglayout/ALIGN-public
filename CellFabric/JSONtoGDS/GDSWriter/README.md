# Python wrapper (cython-based) around GdsWriter

To build:
````
docker build -t gdswriter_python .
````

To run:
````
tar cfv - top.json | docker run --rm -i --mount source=gdsVol,target=/vol ubuntu bash -c "cd /vol && tar xvf -"

docker run --rm --mount source=gdsVol,target=/vol -it gdswriter_python bash -c "source /sympy/bin/activate && cd /src && python gen_gds.py -j /vol/top.json -n top -e MTI && mv top.gds /vol"

docker run -it --env="DISPLAY" --env="QT_X11_NO_MITSHM=1" --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" --mount source=gdsVol,target=/vol darpaalign/klayout bash -c klayout
````