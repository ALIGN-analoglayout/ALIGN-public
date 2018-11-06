# Example Analog Leaf Cell Fabric

The run:

````
docker build -t fabric .

docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric.py && cp mydesign_dr_globalrouting.json /INPUT"

docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"
````
Then visit `localhost:8085`
