# Build

````
docker build -t tally .
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
docker run -it tally bash -c "source sympy/bin/activate && cd /scripts && pytest -- tally.py"
````

# Coverage (tally.py)
````
docker run -p8083:8000 -it tally bash -c "source sympy/bin/activate && cd /scripts && pytest --cov=tally -rs -- tally.py && coverage html && cd htmlcov && python -m http.server"
````
Then visit `localhost:8083` in your brower.

# Experiment with SAT-based Subgraph Isomorphism (monomorphism)

````
docker build -t tally .

docker run --rm -it tally bash -c "source sympy/bin/activate && cd /scripts && pytest -- sat_based_sgi.py"
````
