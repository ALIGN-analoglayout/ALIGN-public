# Example Analog Leaf Cell Fabric

To run fabric generator for a metal0 process:

````
docker build -t fabric .

docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"

docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"
````
Then visit `localhost:8085`

For a process with a horizontal polycon, replace the middle step with:
````
docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric_gf.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"
````

