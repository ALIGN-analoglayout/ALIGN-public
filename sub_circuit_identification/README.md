# subckt identification

## Create a Docker image 
```bash
docker build -t topology .
```

## Run a Python-based test using docker

```bash
docker run --mount source=inputVol,target=/INPUT topology bash -c "source /sympy/bin/activate && cd /DEMO && ./runme.sh ota"
```

## Direct run on terminal
```bash
python ./src/compiler.py --dir ./input_circuit/ -f telescopic_ota.sp --subckt telescopic_ota --flat 0 -U_cap 12 -U_mos 12
```

## Run unit tests in container

Run this.
```bash
docker run --mount source=coverageVol,target=/INPUT -it topology bash -c "source sympy/bin/activate && cd DEMO/src && rm -rf __pycache__ && pytest --cov=. && coverage html && rm -rf /INPUT/htmlcov && mv htmlcov /INPUT"
```

Then this.
```bash
docker run -p 8000:8000 --mount source=coverageVol,target=/INPUT -d with_python bash -c "source sympy/bin/activate && cd INPUT/htmlcov && python -m http.server"
```

To see coverage report look at localhost:8000

<meta http-equiv="refresh" content="0; url="docs/build/html/index.html">

