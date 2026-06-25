*******************************************************
* tb_ac_final.sp -- Cleaned AC Testbench
*******************************************************
.option post=2 
.option nomod
.option measform=3  $ Output measurements in scientific notation
.temp 27


* Universal DUT interface control
.param DUT_HAS_VB2 = 0
.param VB2_DC = 600m
**************** Parameters ***************************
* Bias & Supply
.param VCM=0.6
.param RLEAK=1g

.param FMIN=1
.param FMAX=100G

.include "../design_params.sp"
**************** Supplies & Inputs ********************
VSS  vss 0 0
VDD1 vdd 0 VDD

* Bias Current
IBIAS vdd ibias DC IBIAS
VVB2 vb2 0 DC 'VB2_DC'

* Differential Inputs (AC Magnitude = 1V Total)
* This makes V(out) magnitude equal to the Gain directly.
VINP vp 0 DC VCM AC 0.5 0
VINN vn 0 DC VCM AC 0.5 180

* Helper source to measure differential input easily
EDIFF vdiff 0 vp vn 1

**************** DUT & Load ***************************
.include "../dut_wrapper.sp"
* Pin Order: In+, In-, Out, VDD, VSS, Bias, Vbias2
XU1 vp vn vout vdd vss ibias vb2 DUT_UNIVERSAL

CLOAD  vout vss CL
RLEAK1 vout vss RLEAK

**************** Analysis *****************************
.op
.ac dec 20 FMIN FMAX

**************** Measurements *************************

* 1. DC Gain (A0)
.meas ac A0_MAG  FIND par('vm(vout)/vm(vdiff)') AT=FMIN
.meas ac A0_DB   PARAM='20*log10(A0_MAG)'

* Helpful reusable expressions
* Gain in dB and transfer phase in degrees
.meas ac GAIN_DB_ATF FIND par('20*log10(vm(vout)/vm(vdiff))') AT=FMIN

* 2. Unity Gain Frequency (UGF) using dB crossing
* Prefer FALL=1 for a normal OTA (gain rolls off with frequency)
.meas ac UGF     WHEN par('20*log10(vm(vout)/vm(vdiff))')=0 FALL=1

* 3. Phase Margin (PM)
* IMPORTANT: quote UGF so HSPICE treats it as the frequency value
.meas ac PH_H_RAW FIND par('vp(vout)-vp(vdiff)') AT='UGF'
.meas ac PH_H     PARAM='(PH_H_RAW>180) ? (PH_H_RAW-360) : ((PH_H_RAW<-180) ? (PH_H_RAW+360) : PH_H_RAW)'
.meas ac PM       PARAM='180 + PH_H'

* 4. 3dB Bandwidth
* Use FALL=1 to avoid grabbing a wrong crossing
.meas ac BW_3DB  WHEN par('20*log10(vm(vout)/vm(vdiff))')='A0_DB-3' FALL=1

**************** Gain Margin Measurements ****************

* Frequency where phase crosses -180 degrees (may fail if never reached)
.meas ac FREQ_180  WHEN par('vp(vout)-vp(vdiff)')=-180 CROSS=1

* Quote FREQ_180 so it is interpreted as frequency, not time
.meas ac GAIN_AT_180 FIND par('20*log10(vm(vout)/vm(vdiff))') AT='FREQ_180'

* Gain Margin in dB
.meas ac GM_DB    PARAM='0 - GAIN_AT_180'
.end
