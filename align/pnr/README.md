### Python-based Processing of the PnRdatabase

To install:
```bash
pip install python-gdsii
(cd ../GDSConv && pip install -e .)
(cd ../CellFabric && pip install -e .)
pip install -e .
```
To run the tests:
```bash
pytest -v --capture=no > LOG
```
Look in `LOG` for a listing of violations
n
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
export ALIGN_WORK_DIR=$ALIGN_HOME/build/tmp
rm -rf $ALIGN_WORK_DIR
mkdir $ALIGN_WORK_DIR
cd $ALIGN_WORK_DIR
ln -s <path to general virtual enviornment> .
ln -s ../Makefile
PNRDB_SAVE_STATE= make
```
This will generate flow intermediate files in the `telescopic_ota` directory.
Then run this to generate a visualization JSON file which include global routes (it is put in the ../Viewer/INPUT directory)
```bash
cd $ALIGN_HOME/PnRPython
export DESIGN=telescopic_ota
./gen_viewer_json.py -b $DESIGN -d ../build/tmp/$DESIGN/pnr_output/Results -o ../Viewer/INPUT --draw_grid -l INFO  --json_dir ../build/tmp/$DESIGN/pnr_output/inputs/
```
You can visualize this by running:
```bash
(cd ../Viewer; python -m http.server&)
```
Then visit `localhost:8000?design=telescopic_ota_0` in your browser.

This works with multiple levels of hierarchy if the intermediate JSON files are generated in the correct order.
The script:
```bash
./run_switched_capacitor_filter.sh
```
does the right thing for the hierarchical `switched_capacitor_filter`.
There are still several errors (shorts, opens, etc.)
