*******************************************************
* tb_psrr_minus.sp -- PSRR- Simulation (AC-4 Logic)
*******************************************************
.option post=2 
.option nomod
.option measform=3 
.temp 27


* Universal DUT interface control
.param DUT_HAS_VB2 = 0
.param VB2_DC = 600m
**************** Parameters ***************************

.param VCM     = 0.6         $ Input Common Mode
.param VOFF    = 1m          $ Offset Voltage (Step 4)

* Frequency Range
.param FMIN=10
.param FMAX=100G

* CRITICAL: Update this with your actual DC Gain
.param ADC_GAIN_DB = 20      

**************** Supplies (AC-4 Logic) ****************
* Positive Rail (Stable DC)
VDC_SRC  vdd 0  DC VDD

* Negative Rail (AC Injection)
* Step 3: Source between Ground (0) and Pin (vss)
VAC_NEG  vss 0  DC 0 AC 1    

* Bias Current
IBIAS vdd ibias DC IBIAS
VVB2 vb2 0 DC 'VB2_DC'

**************** Inputs *******************************
* Inputs referenced to Global Ground (0)

* Inverting Input
VINN vn 0 DC VCM

* Non-Inverting Input (+ Offset)
VINP vp 0 DC 'VCM + VOFF'

**************** DUT & Load ***************************
.include "../design_params.sp"
.include "../dut_wrapper.sp"

* Pin Order: In+, In-, Out, VDD, VSS, Bias, Vbias2
Xdut vp vn vout vdd vss ibias vb2 DUT_UNIVERSAL

* Load connected to Global Ground
CLOAD vout 0 CL

**************** Analysis *****************************
.op
.ac dec 20 FMIN FMAX

**************** Measurements *************************
* Measure Gain from Negative Supply to Output
.meas ac APS_MINUS_DB  FIND vdb(vout) AT=FMIN

* Calculate PSRR-
.meas ac PSRR_MINUS_DB PARAM='ADC_GAIN_DB - APS_MINUS_DB'

.end
