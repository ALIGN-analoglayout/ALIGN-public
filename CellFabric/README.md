
# Common Infrastructure for Cell Fabric Construction (routing grids too)

## Install and test locally

```bash
pip install -e .
pytest
```

## Install and test in container

```bash
docker build -t cell_fabric_image .
docker run -it cell_fabric_image bash -c "source general/bin/activate && cd /Cell_Fabric_Common/ && pytest"
```

