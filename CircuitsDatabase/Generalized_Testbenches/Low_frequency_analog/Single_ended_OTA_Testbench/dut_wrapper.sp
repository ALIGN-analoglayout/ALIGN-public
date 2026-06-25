*******************************************************
* dut_wrapper.sp -- Universal DUT Interface Adapter
*******************************************************
*
* Select one DUT netlist from dut/ by changing the include below.
*
* DUT_HAS_VB2 = 0:
*   Underlying DUT pin order is:
*   vp vn vout vdd vss ibias
*
* DUT_HAS_VB2 = 1:
*   Underlying DUT pin order is:
*   vp vn vout vdd vss ibias vb2
*
*******************************************************

.include "dut/5t_ota.sp"

.subckt DUT_UNIVERSAL vp vn vout vdd vss ibias vb2
.if (DUT_HAS_VB2 == 1)
XCORE vp vn vout vdd vss ibias vb2 DUT
.else
XCORE vp vn vout vdd vss ibias DUT
.endif
.ends DUT_UNIVERSAL
