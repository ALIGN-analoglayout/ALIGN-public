# Build

````
docker build -f Dockerfile.tally -t tally .
````
This is different. You need to have the build context be the parent directory because we are doing a `pip install` for the `../Cktgen` directory.
````
docker build -f ./Dockerfile -t satplacer ..
````

# Equalizer Design Example
To run the complete equalizer design example, try:
````
./bottom-up.sh
````
Then visit `localhost:8090`

Or do the individual stages, for example:
````
./flow-dp1x.sh
````
or 
````
python top.py
./flow-top.sh
````


# Test (tally.py)

````
docker run -it tally bash -c "source /sympy/bin/activate && pytest -- /sympy/lib/python3.6/site-packages/tally/tally.py"
````

# Coverage (tally.py)
````
docker run -p8083:8000 -it tally bash -c "source sympy/bin/activate && pytest --cov=tally -rs -- ../sympy/lib/python3.6/site-packages/tally/tally.py && coverage html && cd htmlcov && python -m http.server"
````
Then visit `localhost:8083` in your brower.
