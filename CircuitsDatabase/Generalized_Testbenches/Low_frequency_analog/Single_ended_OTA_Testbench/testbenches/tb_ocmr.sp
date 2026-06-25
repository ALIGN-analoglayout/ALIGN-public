*******************************************************
* tb_ocmr_final.sp - Topology Agnostic Output Range
*******************************************************
.option post=2 nomod accurate=1
.temp 27


* Universal DUT interface control
.param DUT_HAS_VB2 = 0
.param VB2_DC = 600m
************** User / DUT parameters ******************
* Adjust these to match your technology nodes
.param VCM_MID=0.6
.param VDD_VAL=1.0
.param VSS_VAL=0


.include "../design_params.sp"
.include "../dut_wrapper.sp"

**************** Supplies & Bias **********************
VVDD  vdd  0  DC 'VDD_VAL'
VVSS  vss  0  DC 'VSS_VAL'
IB    vdd  vbias DC 'IBIAS'
VVB2 vb2 0 DC 'VB2_DC'

**************** Unity Gain Configuration *************
* We sweep the input; feedback forces Vout to follow it.
V_IN_POS  vip   0  DC 'VCM_MID'
XU1 vip vout vout vdd vss vbias vb2 DUT_UNIVERSAL  $ Vin- (pin 2) tied to Vout (pin 3)

**************** DC Sweep *****************************
* Sweep input from rail to rail
.dc V_IN_POS 0 'VDD_VAL' 0.01

**************** Measurements **************************
* 1. Calculate the small-signal gain (slope) of the buffer.
* In the linear range, the slope should be approx 1.0.
.probe dc buffer_slope=deriv('v(vout)')

* 2. Identify the limits (OCMR).
* We define the limit where the slope drops to 0.8 (20% gain loss).
* This is where the output transistors exit saturation.
.meas dc PEAK_SLOPE MAX deriv('v(vout)')
.meas dc TARGET_SLOPE PARAM='PEAK_SLOPE * 0.8'
.meas dc OCMR_MIN FIND v(vout) WHEN deriv('v(vout)')='TARGET_SLOPE' CROSS=1


*OCMR_MAX is fine
.meas dc TARGET_SLOPE_OCMR_MAX PARAM='PEAK_SLOPE * 0.8'
.meas dc OCMR_MAX FIND v(vout) WHEN deriv('v(vout)')='TARGET_SLOPE_OCMR_MAX' CROSS=LAST


.probe dc VOUT=v(vout) VIN=v(vip) SLOPE=deriv(v(vout))

* 3. Final Range Calculation
.meas dc OCMR_RANGE PARAM='OCMR_MAX - OCMR_MIN'



**************** Probes ********************************
.probe dc v(vout) v(vip)
.end
