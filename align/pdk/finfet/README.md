# 22nm FinFET Technology
This is a mock PDK inspired by [Intel 22nm FinFET Fact Sheet](https://newsroom.intel.com/newsroom/wp-content/uploads/sites/11/2017/09/22-ffl-en-fact-sheet.pdf). PDK abstraction contains only Poly, M1-M6 and V1-V5 layers.

## Usage
```
    schematic2layout.py $ALIGN_HOME/align/pdk/finfet/examples/common_source -p $ALIGN_HOME/align/pdk/finfet -c -l DEBUG
```

## Tests
```
    cd $ALIGN_HOME/tests/pdk/finfet/
    pytest -v 
```

