### Python-based Processing of the PnRdatabase

To install:
```bash
pip install python-gdsii
(cd ../GDSConv && pip install -e .)
(cd ../CellFabric && pip install -e .)
pip install -e .
```
```

To convert to a viewer file:
```bash
gen_viewer_json.py -b telescopic_ota -d ../Bugs/Results	
```

To run the tests:
```bash
pytest -v --capture=no > LOG
```
Look in `LOG` for a listing of violations

To build and test using docker :
```bash
docker build -f ./Dockerfile -t pnrpython_image ..
docker run -it pnrpython_image bash -c "source /general/bin/activate && cd PnRPython && pytest -v -s"
```

Currently these tests are failing because of errors in the code.
