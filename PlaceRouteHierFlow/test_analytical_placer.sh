circuit=$1
./pnr_compiler ./testcase/$circuit $circuit.lef $circuit.v $circuit.map layers.json $circuit 1 0 | tee log

