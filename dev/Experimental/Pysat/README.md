# Build

````
docker build -f Dockerfile.tally -t tally_image .
````
This is different. You need to have the build context be the parent directory because we are doing a `pip install` for the `../Cktgen` directory.
````
docker build -f ./Dockerfile -t satplacer_image ..
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
docker run -it tally_image bash -c "source /general/bin/activate && cd tally && python setup.py test"
````

# Coverage (tally.py)
````
docker run -p8099:8000 -it tally_image bash -c "source general/bin/activate && cd tally && coverage run --source=tally,tests setup.py test && coverage html && cd htmlcov && python -m http.server"
````
Then visit `localhost:8099` in your brower.
