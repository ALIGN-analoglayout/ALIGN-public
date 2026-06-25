Now check the testbench for Common mode rejection ration: *******************************************************
* tb_cmrr.sp -- CMRR Testbench
* Measures Differential Gain, Common Mode Gain, and CMRR
*******************************************************
.option post=2 
.option nomod
.option measform=3
.temp 27


* Universal DUT interface control
.param DUT_HAS_VB2 = 0
.param VB2_DC = 600m
**************** Parameters ***************************
.include "../design_params.sp"
.param V_OFFSET=1m
.param FMIN = 1
.param FMAx = 200G
.param vcm=0.6
.param A0_DIFF_DB=20
**************** Supplies *****************************
VSS  vss 0 0
VDD1 vdd 0 VDD
IBIAS vdd ibias DC IBIAS
VVB2 vb2 0 DC 'VB2_DC'


**************** DUT & Load ***************************
.include "../dut_wrapper.sp"
* Pin Order: In+, In-, Out, VDD, VSS, Bias, Vbias2
XU1 vip vin vout vdd vss ibias vb2 DUT_UNIVERSAL

CLOAD  vout vss CL
RLEAK1 vout vss RLEAK

**************** Stimulus Setup ***********************
* We use a helper source 'V_AC_MODE' to toggle between
* Differential Mode (DM) and Common Mode (CM) without
* needing two separate runs.

* Common Mode DC Level
V_CM_REF n_cm_ref 0 DC VCM

* 1. To Measure CMRR properly, we stimulate Common Mode.
* Vip = Vcm + Vac
* Vin = Vcm + Vac
* (Both inputs move UP together)


* AC Source (Magnitude = 1V)
VAC_CM n_ac_cm 0 DC 0 AC 1

* Input Definitions
* Both inputs receive the AC signal (Common Mode Excitation)
E_VIP vip 0 VOL='v(n_cm_ref) + v(n_ac_cm) + V_OFFSET/2'
E_VIN vin 0 VOL='v(n_cm_ref) + v(n_ac_cm) - V_OFFSET/2'

**************** Analysis *****************************
.op
.ac dec 20 FMIN FMAX

**************** Measurements *************************

* 1. Measure Common Mode Gain (A_cm) at low freq
* A_cm = Vout / Vin_common_mode
.meas ac ACM_MAG  FIND vm(vout) AT=FMIN
.meas ac ACM_DB   PARAM='20*log10(ACM_MAG)'




* 3. Calculate CMRR
* CMRR(dB) = A_diff(dB) - A_cm(dB)
.meas ac CMRR_DB  PARAM='A0_DIFF_DB - ACM_DB'


.end
