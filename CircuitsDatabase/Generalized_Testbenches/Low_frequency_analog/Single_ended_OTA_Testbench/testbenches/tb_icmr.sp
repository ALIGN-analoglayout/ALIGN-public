*******************************************************
* tb_icmr_fixed.sp -- Corrected ICMR testbench
*******************************************************
.option post=2
.option nomod
.temp 27


* Universal DUT interface control
.param DUT_HAS_VB2 = 0
.param VB2_DC = 600m
************** Import Global Parameters ***************
.include "../design_params.sp"

.param VCM_START=0
.param VCM_STOP='VDD'
.param VCM_STEP=10m
.param VDS_SAFETY=0.02
.param VCM_NOM = 'min(max(VCM_START, VDD/2), VCM_STOP)'

**************** Include DUT **************************
.include "../dut_wrapper.sp"

**************** Supplies *****************************
VVDD  vdd  0   'VDD'
VVSS  vss  0   'VSS'
IB    vdd  vbias  DC 'IBIAS'
VVB2 vb2 0 DC 'VB2_DC'

**************** Common-mode input source **************
VCM   vcm  0   DC 0
VSH1  vip  vcm 0

**************** DUT instance (FIXED) ******************
* Pin Order: In+, In-, Out, VDD, VSS, Bias, Vbias2
XU1 vip vout vout vdd vss vbias vb2 DUT_UNIVERSAL


**************** DC sweep ******************************
.dc VCM 'VCM_START' 'VCM_STOP' 'VCM_STEP'

**************** True Black-Box ICMR Monitoring ********
* 1. Voltage Tracking Error Node (Catches upper limit gain collapse)
E_error error_node 0 VOL = 'abs(v(vout) - v(vcm))'
R_err error_node 0 1Meg 

* 2. Total Supply Current Node (Catches lower limit tail starvation)
* Using abs() to prevent any negative polarity issues depending on VVDD definition
E_idd idd_node 0 VOL = 'abs(i(VVDD))'
R_idd idd_node 0 1Meg

**************** Probes ********************************
.probe dc v(vcm) v(vout) v(error_node) v(idd_node)

**************** Measurements **************************
* 1. Measure nominal baseline at mid-supply (VDD/2)
.meas dc NOM_ERR FIND v(error_node) AT='VCM_NOM'
.meas dc NOM_IDD FIND v(idd_node) AT='VCM_NOM'

* 2. Define Strict Limits
* Fail if tracking error worsens by 10mV, or if total current drops by 5%
.meas dc ERR_LIMIT PARAM='NOM_ERR + 0.010'
.meas dc IDD_LIMIT PARAM='NOM_IDD * 0.95'

* 3. Extract ICMR
* ICMR_MIN: The point where the tail current recovers to 95% of nominal
.meas dc ICMR_MIN FIND v(vcm) WHEN v(idd_node)='IDD_LIMIT' RISE=1
*.meas dc ICMR_MIN FIND v(vcm) WHEN v(error_node)='ERR_LIMIT' FALL=1

* ICMR_MAX: The point where tracking error breaks out of the 10mV tolerance
.meas dc ICMR_MAX FIND v(vcm) WHEN v(error_node)='ERR_LIMIT' RISE=LAST

* Total Range
.meas dc ICMR_RANGE PARAM='ICMR_MAX - ICMR_MIN'
.end
