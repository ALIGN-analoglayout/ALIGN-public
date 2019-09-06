### Cap Placer Generates Off Grid Terminals

Here is an example:

```bash
../PlaceRouteHierFlow/pnr_compiler switched_capacitor_filter switched_capacitor_filter.{lef,v,map} FinFET_Mock_PDK_Abstraction.json switched_capacitor_filter 1 0 > LOG
```

To visualize the DB in the viewer (install the package in PlaceRouteHierFlow/PnRPython first):
```bash
./gen_viewer_json.py -b switched_capacitor_filter
```
The file `switched_capacitor_filter_dr_globalrouting.json` is generated.
To view, you can do the following:
```bash
cp switched_capacitor_filter_dr_globalrouting.json ../CellFabric/Viewer/INPUT
(cd ../CellFabric/Viewer && python -m http.server&)
```
Then visit `localhost:8000?design=switched_capacitor_filter` in your browser.

Add the option `-c` if you instead want to check for opens, shorts, etc.
```bash
./gen_viewer_json.py -b switched_capacitor_filter -c
```



