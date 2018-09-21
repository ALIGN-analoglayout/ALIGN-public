# Simple Layout Viewer

Currently reads a JSON file named /public/INPUT/mydesign_dr_globalrouting.json (need to change this.)

To build in docker, build upon "with_python_protobuf" (see the Build/ subdirectory):

````bash
docker build -t viewer_image .
````

To run using docker, try:
````bash
docker run -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server"
````
Then connect your browser (Chrome) to the server using localhost:8000.
If you want to use a different port number (not 8000), you can either start the server on a different port:
````bash
docker run -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server 8081"
````
or map the ports using a docker command line argument.
````bash
docker run -p 8081:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server"
````

This runs with the example JSON file.
To mount a different JSON, mount a Docker volume on top of /public/INPUT.
This will be something like:
````bash
docker run --mount source=myJSONVol,target=/public/INPUT -p8082:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server"
````
You'll need to have written your new JSON file to the docker volume ahead of time.
You can do it like this (there is another json file in the subdirectory larger_example)
````bash
cd larger_example
tar cvf - mydesign_dr_globalrouting.json | docker run --mount source=myJSONVol,target=/vol -i ubuntu bash -c "cd /vol; tar xvf -"
````

Use docker stop and docker rm to remove these servers when you are done.
