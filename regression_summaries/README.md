# Regression Methodology

First run a regression.
I use:
```bash
export ALIGN_WORK_DIR=$ALIGN_HOME/work
cd $ALIGN_HOME
pytest -n 16 --runnightly -vv -- tests/integration/test_all.py 
```
On of these takes forever (TI_SAR) so I kill the run when only one of the sixteen processes is running.

Then
```bash
cd $ALIGN_WORK_DIR/FinFET14nm_Mock_PDK
analyze_regression.py
```
This produces a `summary.csv` file that we can now compare to older runs.
```bash
pip install dash
cd $ALIGN_HOME/regression_summaries
./render_table.py -0 summary_2021_04_23.csv -1 $ALIGN_WORK_DIR/FinFET14nm_Mock_PDK/summary.csv
```
Follow the instructions to visit the webpage with the comparison to the previous summary (visit `localhost:8050`)
You should be able to sort and filter each column (try `> 0` in one of the numeric columns)

# Viewing layouts as well

If you start up the viewer, you can use `render_table.py` to quickly view layouts by click on cells in the table.
```bash
(cd $ALIGN_HOME/Viewer; python -m http.server&)
```

Then run `render_table.py` with directory arguments:
```bash
cd $ALIGN_HOME/regression_summaries
./render_table.py -0 summary_2021_04_23.csv -1 $ALIGN_WORK_DIR/FinFET14nm_Mock_PDK/summary.csv -d1 $ALIGN_WORK_DIR/FinFET14nm_Mock_PDK
```
If you click on any cell in a columns whose name ends with '_y', then the corresponding layout will be rendered in a new web browser tab. If you also supply a '-d0' directory, then you click on cells in columns with a '_x' suffix and get the reference layouts as well.
