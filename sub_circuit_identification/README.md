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
chmod +x runme.sh
./runme.sh ota
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


# Usage slides:
https://docs.google.com/presentation/d/1NbXXx6vI8KNOhjRaRHlG57hA6jdRX_BA-xOshC8XbzU/edit?usp=sharing
