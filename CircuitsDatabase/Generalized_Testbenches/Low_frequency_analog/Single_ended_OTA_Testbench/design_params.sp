*******************************************************
* design_params.sp -- Global Circuit Parameters
*******************************************************

* --- Power Supplies ---
.param VDD = 1.0
.param VSS = 0.0

* --- Biasing ---
* This is your reference tail current. 
* Ensure this matches your cm_ota.sp biasing requirements.
.param IBIAS = 5u

* --- Loading ---
* Standard load for area/speed trade-offs
.param CL = 500f
.param c0 = 0.5p
.param r0 = 2.5k
* --- Leakage/Safety ---
* High resistance to prevent floating nodes during DC convergence
.param RLEAK = 100Meg

* --- Timing Constants ---
* Default UGF used as a fallback if the AC sim hasn't run yet
.param UGF_DEFAULT = 50Meg

*******************************************************
* Optimization/Simulator Options
*******************************************************
.option post=2      $ Enables waveform viewing (RTA/Custom WaveView)
.option nomod       $ Clean up the .lis file by hiding model parameters
.option probe       $ Only save signals explicitly requested in .probe
.option runlvl=5

*******************************************************
* Device parameters
*******************************************************
* Placeholder MOS sizes for the DUT library.
* Replace these placeholder lengths and widths with the actual sizes for your
* selected DUT before running the testbenches.
.param m0_l=180n
.param m0_w=1u
.param m1_l=180n
.param m1_w=1u
.param m2_l=180n
.param m2_w=1u
.param m3_l=180n
.param m3_w=1u
.param m4_l=180n
.param m4_w=1u
.param m5_l=180n
.param m5_w=1u
.param m6_l=180n
.param m6_w=1u
.param m7_l=180n
.param m7_w=1u
.param m8_l=180n
.param m8_w=1u
.param m9_l=180n
.param m9_w=1u
.param m10_l=180n
.param m10_w=1u
