*******************************************************
* tb_op_params.sp -- Forced Parameter Extraction
*******************************************************
.option post=2      
.option nomod
.option measform=3
.option results
.temp 27


* Universal DUT interface control
.param DUT_HAS_VB2 = 0
.param VB2_DC = 600m
* --- CRITICAL FORMATTING OPTIONS ---
* ingold=2: Forces strict scientific notation (e.g. 1.0e-09), easier for Python.
* numdgt=10: High precision.
* width=5000: Prevents table columns from wrapping to the next line.
.option ingold=2 
.option numdgt=10
.option width=5000 

**************** Parameters ***************************
.param VCM=7.021553e-01
.param dummy_var=0
.include "../design_params.sp"

**************** Supplies & Inputs ********************
VSS  vss 0 0
VDD1 vdd 0 VDD
IBIAS vdd ibias DC IBIAS
VVB2 vb2 0 DC 'VB2_DC'
VINP vp 0 DC VCM 
VINN vn 0 DC VCM 

**************** DUT ***************************

.include "../dut_wrapper.sp"
* Pin Order: In+, In-, Out, VDD, VSS, Bias, Vbias2
XU1 vp vn vout vdd vss ibias vb2 DUT_UNIVERSAL
CLOAD  vout vss CL

**************** Analysis *****************************
* Dummy sweep to force print output
.dc dummy_var 0 0 1

**************** Operating Point Print ****************
* Note: Ensure all parameters for a device are on one CONTINUOUS line 

