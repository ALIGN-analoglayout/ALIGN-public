# Layout results from ALIGN on all the running testcases.
Each design folder contains ALIGN generated post placement (.pl/.plt files) and post routing results (.json).
You can see the final layout image (<design_name>\_0.png) of designs from [example](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/examples) directory in the respective directories.

To see the results in KLayout you can download the gds.json file and convert it to gds using [gds converter](https://github.com/ALIGN-analoglayout/ALIGN-public/blob/bug/compiler/align/gdsconv/gds2json.py)

For each major code update we run comparison between this golden data  (<design_name>\_0.gds.json ) and new results. Once new results are verified by designers and seem to have better layout we update this golden dataset. 
