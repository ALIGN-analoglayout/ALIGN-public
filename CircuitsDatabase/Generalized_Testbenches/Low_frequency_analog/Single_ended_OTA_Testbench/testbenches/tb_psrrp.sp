*******************************************************
* tb_psrr_plus_clean.sp -- PSRR+ Simulation
*******************************************************
.option post=2 
.option nomod
.option measform=3 
.temp 27


* Universal DUT interface control
.param DUT_HAS_VB2 = 0
.param VB2_DC = 600m
**************** Parameters ***************************
.param VCM     = 0.6         $ Midpoint of ICMR (Step 2)
.param VOFF    = 1m          $ Offset Voltage (Step 4)

* FREQUENCY RANGE (Step 5)
.param FMIN=10
.param FMAX=100G

* REQUIRED: Enter DC Gain from previous simulation here (Step 7)
.param ADC_GAIN_DB = 20      $ <--- UPDATE THIS VALUE

**************** Supplies (Step 3) ********************
* Negative Rail
VSS  vss 0 0

* Positive Rail with AC Injection (Step 3)
* We stack AC source on top of DC supply.
VDC_SRC  vdd_node 0        DC VDD
VAC_SRC  vdd      vdd_node AC 1       $ <--- AC Perturbation on VDD

* Bias Current
IBIAS vdd ibias DC IBIAS
VVB2 vb2 0 DC 'VB2_DC'

**************** Inputs (Step 2 & 4) ******************
* Inputs are AC Grounded (AC=0)

* Inverting Input (-)
VINN vn 0 DC VCM

* Non-Inverting Input (+)
* Apply Offset here as per Step 4
VINP vp 0 DC 'VCM + VOFF'

**************** DUT & Load ***************************
.include "../design_params.sp"
.include "../dut_wrapper.sp"

* Pin Order: In+, In-, Out, VDD, VSS, Bias, Vbias2
Xdut vp vn vout vdd vss ibias vb2 DUT_UNIVERSAL

CLOAD vout 0 CL

**************** Analysis (Step 5) ********************
.op
.ac dec 20 FMIN FMAX

**************** Measurements (Steps 6 & 7) ***********

* 1. Measure Power Supply Gain (A_ps+) at FMIN (Step 6)
.meas ac APS_PLUS_DB  FIND vdb(vout) AT=FMIN

* 2. Calculate PSRR+ (Step 7)
* PSRR+ = DC_Gain - Power_Supply_Gain
.meas ac PSRR_PLUS_DB PARAM='ADC_GAIN_DB - APS_PLUS_DB'

.end
