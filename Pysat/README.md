# Build

````
docker build -t tally .
````

# Test

````
docker run -it tally bash -c "source sympy/bin/activate && cd /scripts && pytest -- tally.py euler.py global_router.py"
````

# Coverage
````
docker run -p8083:8000 -it tally bash -c "source sympy/bin/activate && cd /scripts && pytest --cov=tally --cov=euler --cov=global_router -rs -- tally.py euler.py global_router.py && coverage html && cd htmlcov && python -m http.server"
````
Then visit `localhost:8083` in your brower.

# Include slow tests
````
docker run -p8083:8000 -it tally bash -c "source sympy/bin/activate && cd /scripts && pytest --cov=tally --cov=euler --cov=global_router --runslow --duration=3 -- tally.py euler.py global_router.py && coverage html && cd htmlcov && python -m http.server"
````