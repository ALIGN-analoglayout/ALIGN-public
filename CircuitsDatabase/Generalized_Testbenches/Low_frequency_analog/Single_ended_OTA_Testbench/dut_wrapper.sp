*******************************************************
* dut_wrapper.sp -- Universal DUT Interface Adapter
*******************************************************
*
* Selected DUT for this run: cascode OTA.
*
* DUT_HAS_VB2 = 0:
*   Underlying DUT pin order is:
*   vp vn vout vdd vss ibias
*
* DUT_HAS_VB2 = 1:
*   Underlying DUT pin order is:
*   vp vn vout vdd vss ibias vb2
*   The current seven-pin cascode DUTs have core input
*   polarity is reversed relative to the universal interface.
*   Swap vp/vn here so every testbench sees vp as non-inverting
*   and vn as inverting.
*
*******************************************************

.include "dut.sp"

.subckt DUT_UNIVERSAL vp vn vout vdd vss ibias vb2
.if (DUT_HAS_VB2 == 1)
XCORE vn vp vout vdd vss ibias vb2 DUT
.else
XCORE vp vn vout vdd vss ibias DUT
.endif
.ends DUT_UNIVERSAL
