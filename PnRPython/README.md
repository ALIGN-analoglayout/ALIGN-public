### Python-based Processing of the PnRdatabase

To install:
```bash
pip install -e .
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
