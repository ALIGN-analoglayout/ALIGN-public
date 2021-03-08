Running the tool:
Command: python3 run.py -design <design_name> -sim ac1ac2ac3dc1tran1

ac1ac2ac3dc1tran1 indicates which simulations to run. For example,
python3 run.py -design OTA_5T -sim 10000
THe above command will only run the "ac1" simulation and will only consider the performance specifications mentioned in the design_name.mdl file. More details about the mdl files is included below.

Example commands:
- python3 run.py -design OTA_5T -sim 11100
- python3 run.py -design OTA_telescopic -sim 10000
- python3 run.py -design OTA_two_stage -sim 11101

Input files:
Primary:
design.sp: The circuit netlist
design_tb.sp: The testbench for the circuit
nets_under_test.txt: This file includes the names of the nets under consideration
spec_limits.csv:
- Includes the limit of the performance specification under test in CSV format.
- For example, if "gain" is a performance specification under observation, a min and max limit has to be written for "gain" in a column of this file.

MDLForFSP/design.mdl:
- This mdl file is used to specify the performance specifications to be observed from "ac1" simulation in the "feature space pruning" stage.
- The specification to be observed are specified with an "export" expression.
- This file is used for gain, bandwidth, unity gain frequency, phase margin, and gain margin.

MDLForML/design.mdl:
- This mdl file is used to specify the performance specifications to be observed from "ac1" simulation in the "ML classification" stage.
- The specification to be observed are specified with an "export" expression.
- This file is used for gain, bandwidth, unity gain frequency, phase margin, and gain margin.

Secondary:
MDLForFSP/design_ac_2.mdl:
- This mdl file is used to specify the performance specifications to be observed from "ac2" simulation.
- The specification to be observed are specified with an "export" expression.
- This file used for common mode rejection ratio.

MDLForFSP/design_ac_3.mdl:
- This mdl file is used to specify the performance specifications to be observed from "ac3" simulation.
- The specification to be observed are specified with an "export" expression.
- This file is used for power supply rejection ratio.

MDLForFSP/design_dc_1.mdl:
- This mdl file is used to specify the performance specifications to be observed from "dc1" simulation.
- The specification to be observed are specified with an "export" expression.
- This file is used for input common mode range.

MDLForFSP/design_tran_1.mdl:
- This mdl file is used to specify the performance specifications to be observed from "ac1" simulation.
- The specification to be observed are specified with an "export" expression.
- This file is used slew rate.

Output files:
"trained_model_*".sav:
- These files holds the trained ML model for each performance specifications. These files will be used in evaluating placement layouts.
