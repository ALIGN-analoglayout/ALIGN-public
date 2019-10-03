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

### Visualize and check for Opens/Shorts in an examples run

Run the example, say `telescopic_ota` using the compose-based make flow.
```bash
export ALIGN_HOME=<path to ALIGN-public directory>
export ALIGN_WORK_DIR=$ALIGN_HOME/compose/tmp
rm -rf $ALIGN_WORK_DIR
mkdir $ALIGN_WORK_DIR
cd $ALIGN_WORK_DIR
ln -s <path to general virtual enviornment> .
ln -s ../Makefile
PNRDB_SAVE_STATE= PNRDB_ADR_MODE= make
```
This will generate flow intermediate files in the `telescopic_ota` directory.
Then run this to generate a visualization JSON file which include global routes (it is put in the ../Viewer/INPUT directory)
```bash
cd $ALIGN_HOME/PnRPython
export DESIGN=telescopic_ota
./gen_viewer_json.py -b $DESIGN -d ../compose/tmp/$DESIGN/pnr_output/Results -o ../Viewer/INPUT --draw_grid -l INFO  --json_dir ../compose/tmp/$DESIGN/pnr_output/inputs/ --global_route_json ../compose/tmp/$DESIGN/pnr_output/Results/${DESIGN}_GcellGlobalRoute_0.json 
```
You can visualize this by running:
```bash
(cd ../Viewer; python -m http.server&)
```
Then visit `localhost:8000?design=telescopic_ota_0` in your browser.

To run the short and open checker, you can use this command line:
```bash
./gen_viewer_json.py -b telescopic_ota -d ../compose/tmp/telescopic_ota/pnr_output/Results -o ../Viewer/INPUT --draw_grid -l INFO  --json_dir ../compose/tmp/telescopic_ota/pnr_output/inputs/ --check
```
Here we don't include the global routes (no `--global_route_json` option).

This probably only works with one level of hierarchy (routing leaf cells together.)

Currently there are a number of OPENs: `net10`, `voutn`, and `voutp`.
There seems to be no connection between the leaf cells.
