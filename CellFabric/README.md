
# Common Infrastructure for Cell Fabric Construction (routing grids too)

## Install and test locally

```bash
pip install -e .
pytest
```

## Install and test in container

```bash
rm -rf __pycache__/ */__pycache__
docker build -t cell_fabric_image .
docker run -it cell_fabric_image bash -c "source general/bin/activate && cd /src/ && pytest"
```

## To visualize JSON created by tests

The tests produce mulitple JSON files. For example, to visualize `tests/__json_via_set_cand` do the following (if done locally):
```bash
cp tests/__json_via_set_cand Viewer/INPUT/mydesign_dr_globalrouting.json
(cd Viewer && python -m http.server)&
```
Then open up the web browser `localhost:8000`.

