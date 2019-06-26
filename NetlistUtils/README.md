
# Common Infrastructure for Circuit parsing / generation

## Install and test locally

```bash
pip install -e .
pytest
```

## Install and test in container

```bash
rm -rf __pycache__/ */__pycache__
docker build -t netlist_utils_image -f ./Dockerfile ..
docker run -it netlist_utils_image bash -c "source general/bin/activate && cd /NetlistUtils/ && pytest"
```
