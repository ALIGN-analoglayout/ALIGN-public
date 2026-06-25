*******************************************************
* tb_sr_icmr.sp -- Slew Rate Testbench (Slide Compliant)
* Method: Full Range Step (ICMR Min <-> ICMR Max)
* Measure: 10% to 90% Transition Time
*******************************************************
.option post=2 
.option nomod
.option measform=3
.temp 27


* Universal DUT interface control
.param DUT_HAS_VB2 = 0
.param VB2_DC = 600m
**************** 1. Includes **************************
* Using your template filenames
.include "../design_params.sp"
.include "../dut_wrapper.sp"

**************** 2. Parameters & Timing ***************
* --- ICMR LEVELS (From your previous simulation) ---
.param VICMR_MAX = 847m 
.param VICMR_MIN = 445m 

* --- Timing Setup ---
* Using the specific UGF you provided
.param UGF_EST = 3.777370e+07
.param T_PERIOD = '2 * (1/UGF_EST)'

* Rise time for the input edge
.param T_RISE   = 'T_PERIOD / 100'

* Simulation Duration
.param T_START = 'T_PERIOD/2'
.param T_STOP  = 'T_START + 2*T_PERIOD'

**************** 3. Supplies **************************
VSS   vss 0 0
VDD1  vdd 0 VDD
IBIAS vdd ibias DC IBIAS
VVB2 vb2 0 DC 'VB2_DC'

**************** 4. Stimulus (ICMR Sweep) *************
* Toggles between VICMR_MIN and VICMR_MAX
V_IN_POS vip 0 PWL(
+ 0                       VICMR_MIN
+ 'T_START'               VICMR_MIN
+ 'T_START + T_RISE'      VICMR_MAX
+ 'T_START + T_PERIOD'    VICMR_MAX
+ 'T_START + T_PERIOD + T_RISE'  VICMR_MIN
+ 'T_STOP'                VICMR_MIN
+ )

**************** 5. DUT Configuration *****************
* Unity Gain Buffer Configuration
* Pin Order: In+, In-, Out, VDD, VSS, Bias, Vbias2
XU1 vip vout vout vdd vss ibias vb2 DUT_UNIVERSAL

**************** 6. Load ******************************
CLOAD  vout vss CL
RLEAK1 vout vss RLEAK

**************** 7. Analysis **************************
.param T_STEP = 'T_RISE / 5'
.tran T_STEP T_STOP

**************** 8. Measurements (10-90% Method) ******

* --- RISING EDGE SLEW RATE ---
.param T_RISE_START = 'T_START'
.param T_RISE_END   = 'T_START + T_PERIOD'

.meas tran V_RISE_0   FIND v(vout) AT='T_RISE_START'
.meas tran V_RISE_100 MAX  v(vout) FROM='T_RISE_START' TO='T_RISE_END'

.meas tran V_TH_10_R PARAM='V_RISE_0 + 0.1 * (V_RISE_100 - V_RISE_0)'
.meas tran V_TH_90_R PARAM='V_RISE_0 + 0.9 * (V_RISE_100 - V_RISE_0)'

.meas tran T_10_R WHEN v(vout)=V_TH_10_R RISE=1 FROM='T_RISE_START' TO='T_RISE_END'
.meas tran T_90_R WHEN v(vout)=V_TH_90_R RISE=1 FROM='T_RISE_START' TO='T_RISE_END'

.meas tran SR_POS_Vus PARAM='(V_TH_90_R - V_TH_10_R) / (T_90_R - T_10_R) * 1e-6'


* --- FALLING EDGE SLEW RATE ---
.param T_FALL_START = 'T_START + T_PERIOD'
.param T_FALL_END   = 'T_STOP'

.meas tran V_FALL_100 FIND v(vout) AT='T_FALL_START'
.meas tran V_FALL_0   MIN  v(vout) FROM='T_FALL_START' TO='T_FALL_END'

.meas tran V_TH_90_F PARAM='V_FALL_0 + 0.9 * (V_FALL_100 - V_FALL_0)'
.meas tran V_TH_10_F PARAM='V_FALL_0 + 0.1 * (V_FALL_100 - V_FALL_0)'

.meas tran T_90_F WHEN v(vout)=V_TH_90_F FALL=1 FROM='T_FALL_START' TO='T_FALL_END'
.meas tran T_10_F WHEN v(vout)=V_TH_10_F FALL=1 FROM='T_FALL_START' TO='T_FALL_END'

.meas tran SR_NEG_Vus PARAM='abs( (V_TH_90_F - V_TH_10_F) / (T_90_F - T_10_F) ) * 1e-6'

.end
