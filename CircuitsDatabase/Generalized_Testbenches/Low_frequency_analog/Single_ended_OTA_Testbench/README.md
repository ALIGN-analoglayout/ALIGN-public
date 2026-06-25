# Single-Ended OTA Testbench Suite

This directory contains reusable HSPICE testbenches for single-ended operational transconductance amplifiers (OTAs). The decks use a common DUT wrapper so the same measurements can be run on multiple OTA topologies with the same external pin convention.

## Directory Contents

| Path | Purpose |
| --- | --- |
| `dut/` | OTA DUT netlists and reference schematic images. Each netlist defines a `.subckt DUT ...`. |
| `testbenches/` | Main AC, DC, transient, CMRR, PSRR, ICMR, OCMR, slew-rate, and operating-point testbenches. |
| `design_params.sp` | Shared supply, bias, load, simulator, and device sizing parameters. |
| `dut_wrapper.sp` | Universal adapter that instantiates the selected `DUT` netlist as `DUT_UNIVERSAL`. |
| `tb_ac.sp` | Top-level copy of the AC testbench using root-relative includes. |

## DUT Library

All DUTs expose a single-ended output and differential inputs. The default DUT selected by `dut_wrapper.sp` is `dut/5t_ota.sp`.

| DUT | Netlist | Wrapper setting | Image |
| --- | --- | --- | --- |
| Two-stage OTA | `dut/2s_ota.sp` | `DUT_HAS_VB2 = 0` | ![Two-stage OTA](dut/2s_ota.png) |
| Five-transistor OTA | `dut/5t_ota.sp` | `DUT_HAS_VB2 = 0` | ![Five-transistor OTA](dut/5t_ota.png) |
| Cascode OTA | `dut/cascode_ota.sp` | `DUT_HAS_VB2 = 1` | ![Cascode OTA](dut/cascode_ota.png) |
| Current-mirror OTA | `dut/cm_ota.sp` | `DUT_HAS_VB2 = 0` | ![Current-mirror OTA](dut/cm_ota.png) |
| Low-voltage cascode OTA | `dut/lv_cas_ota.sp` | `DUT_HAS_VB2 = 1` | ![Low-voltage cascode OTA](dut/lv_cas_ota.png) |

### DUT Pin Conventions

The raw DUT netlists use one of two pin lists:

```spice
* DUT_HAS_VB2 = 0
.subckt DUT vp vn vout vdd vss ibias

* DUT_HAS_VB2 = 1
.subckt DUT vp vn vout vdd vss ibias vb2
```

The wrapper always exports this seven-pin interface:

```spice
.subckt DUT_UNIVERSAL vp vn vout vdd vss ibias vb2
```

For DUTs without `vb2`, the wrapper ignores the `vb2` pin.

## Selecting a DUT

Edit `dut_wrapper.sp` and change the include line:

```spice
.include "dut/5t_ota.sp"
```

Then set `DUT_HAS_VB2` in the testbench:

```spice
.param DUT_HAS_VB2 = 0   $ 2s_ota, 5t_ota, cm_ota
.param DUT_HAS_VB2 = 1   $ cascode_ota, lv_cas_ota
```

For cascode-style DUTs, also set the second bias voltage:

```spice
.param VB2_DC = 600m
```

Important: `design_params.sp` currently defines sizing parameters only for `m0` through `m5`. If the selected DUT uses devices such as `m6`, `m7`, or `m10`, add matching parameters such as:

```spice
.param m6_l=180n
.param m6_w=1u
.param m7_l=180n
.param m7_w=1u
```

## Common Parameters

Key shared parameters in `design_params.sp`:

| Parameter | Default | Meaning |
| --- | ---: | --- |
| `VDD` | `1.0` | Positive supply voltage. |
| `VSS` | `0.0` | Negative supply or ground reference. |
| `IBIAS` | `5u` | Bias current source value. |
| `CL` | `500f` | Output load capacitance. |
| `RLEAK` | `100Meg` | High-value leak resistor for floating-node convergence. |
| `UGF_DEFAULT` | `50Meg` | Fallback unity-gain estimate for timing-oriented tests. |

The DUT devices use technology model names such as `nch_lvt` and `pch_lvt`. Add the required PDK model include or library statement before running the decks, either in the testbench, in `design_params.sp`, or through your simulator setup.

## Running the Testbenches

Run from this directory unless your HSPICE setup resolves `.include` paths relative to the input file. The testbenches under `testbenches/` include shared files with `../...`; the top-level `tb_ac.sp` is provided as a root-level AC deck.

Example commands:

```bash
# Root-level AC deck
hspice -i tb_ac.sp -o runs/ac_5t

# Main testbench directory decks
hspice -i testbenches/tb_ac.sp    -o runs/ac
hspice -i testbenches/tb_cmrr.sp  -o runs/cmrr
hspice -i testbenches/tb_icmr.sp  -o runs/icmr
hspice -i testbenches/tb_ocmr.sp  -o runs/ocmr
hspice -i testbenches/tb_psrrp.sp -o runs/psrrp
hspice -i testbenches/tb_psrrn.sp -o runs/psrrn
hspice -i testbenches/tb_sr.sp    -o runs/slew_rate
hspice -i testbenches/tb_op.sp    -o runs/op
```

Typical HSPICE outputs include `.lis` logs, `.mt*` measurement files, and waveform databases because the decks set `.option post=2`.

## Recommended Flow

1. Select the DUT in `dut_wrapper.sp`.
2. Set `DUT_HAS_VB2` and `VB2_DC` in each testbench as needed.
3. Confirm all DUT sizing parameters are defined in `design_params.sp`.
4. Add or enable the correct PDK model library.
5. Run `tb_ac.sp` first to obtain low-frequency gain, UGF, phase margin, bandwidth, and gain margin.
6. Use the AC result values to update dependent decks:
   - Set `A0_DIFF_DB` in `tb_cmrr.sp`.
   - Set `ADC_GAIN_DB` in `tb_psrrp.sp` and `tb_psrrn.sp`.
   - Set `UGF_EST`, `VICMR_MIN`, and `VICMR_MAX` in `tb_sr.sp`.
7. Run the DC range tests (`tb_icmr.sp`, `tb_ocmr.sp`) and transient slew-rate test (`tb_sr.sp`).

## Testbench Summary

| Testbench | Analysis | Main measurements | Purpose |
| --- | --- | --- | --- |
| `tb_ac.sp` | `.op`, `.ac` | `A0_DB`, `UGF`, `PM`, `BW_3DB`, `GM_DB` | Open-loop small-signal gain and stability. |
| `tb_cmrr.sp` | `.op`, `.ac` | `ACM_DB`, `CMRR_DB` | Common-mode rejection. |
| `tb_icmr.sp` | `.dc` | `ICMR_MIN`, `ICMR_MAX`, `ICMR_RANGE` | Valid input common-mode range. |
| `tb_ocmr.sp` | `.dc` | `OCMR_MIN`, `OCMR_MAX`, `OCMR_RANGE` | Valid output common-mode swing in unity feedback. |
| `tb_psrrp.sp` | `.op`, `.ac` | `APS_PLUS_DB`, `PSRR_PLUS_DB` | Rejection of positive-supply ripple. |
| `tb_psrrn.sp` | `.op`, `.ac` | `APS_MINUS_DB`, `PSRR_MINUS_DB` | Rejection of negative-supply ripple. |
| `tb_sr.sp` | `.tran` | `SR_POS_Vus`, `SR_NEG_Vus` | Positive and negative slew rate. |
| `tb_op.sp` | `.dc` dummy sweep | Operating-point listing | Device operating-point extraction. |

## Measurement Fundamentals

### AC Gain and Stability (`tb_ac.sp`)

The testbench applies a differential AC input with total magnitude of 1 V:

```spice
VINP vp 0 DC VCM AC 0.5 0
VINN vn 0 DC VCM AC 0.5 180
EDIFF vdiff 0 vp vn 1
```

Because the differential input magnitude is 1 V, `vm(vout)/vm(vdiff)` directly gives differential gain. The deck measures:

| Metric | How it is measured |
| --- | --- |
| `A0_MAG` | Low-frequency gain at `FMIN`. |
| `A0_DB` | `20*log10(A0_MAG)`. |
| `UGF` | Frequency where gain crosses 0 dB. |
| `PH_H_RAW` | Output phase minus input differential phase at `UGF`. |
| `PM` | `180 + PH_H`, after phase wrapping. |
| `BW_3DB` | Frequency where gain falls to `A0_DB - 3 dB`. |
| `GM_DB` | Negative of gain at the first -180 degree phase crossing. |

### CMRR (`tb_cmrr.sp`)

The common-mode test drives both inputs with the same AC signal while keeping a small DC input offset:

```spice
E_VIP vip 0 VOL='v(n_cm_ref) + v(n_ac_cm) + V_OFFSET/2'
E_VIN vin 0 VOL='v(n_cm_ref) + v(n_ac_cm) - V_OFFSET/2'
```

The deck measures common-mode gain at `FMIN`:

```spice
.meas ac ACM_MAG FIND vm(vout) AT=FMIN
.meas ac ACM_DB  PARAM='20*log10(ACM_MAG)'
.meas ac CMRR_DB PARAM='A0_DIFF_DB - ACM_DB'
```

Update `A0_DIFF_DB` from the AC gain test before trusting `CMRR_DB`.

### ICMR (`tb_icmr.sp`)

The input common-mode voltage is swept from `VCM_START` to `VCM_STOP`. The DUT is connected as a unity-gain follower:

```spice
XU1 vip vout vout vdd vss vbias vb2 DUT_UNIVERSAL
```

Two black-box indicators are monitored:

| Indicator | Meaning |
| --- | --- |
| `error_node = abs(v(vout) - v(vcm))` | Output tracking error in unity feedback. |
| `idd_node = abs(i(VVDD))` | Total supply current. |

The lower ICMR limit is found when supply current rises back to 95% of its nominal mid-supply value. The upper ICMR limit is found when tracking error exceeds nominal error by 10 mV.

### OCMR (`tb_ocmr.sp`)

The OTA is configured as a unity-gain buffer and the input is swept rail-to-rail. The output should follow the input with slope near 1 in the valid output range.

The deck computes:

```spice
PEAK_SLOPE = max(deriv(v(vout)))
TARGET_SLOPE = 0.8 * PEAK_SLOPE
```

`OCMR_MIN` and `OCMR_MAX` are the first and last output voltages where the buffer slope crosses the 80% target. This approximates the output swing range before the output stage loses strong linear tracking.

### PSRR+ (`tb_psrrp.sp`)

The inputs are AC-grounded and a 1 V AC perturbation is injected on the positive supply:

```spice
VDC_SRC vdd_node 0 DC VDD
VAC_SRC vdd vdd_node AC 1
```

The deck measures output response to positive-supply ripple:

```spice
.meas ac APS_PLUS_DB  FIND vdb(vout) AT=FMIN
.meas ac PSRR_PLUS_DB PARAM='ADC_GAIN_DB - APS_PLUS_DB'
```

Set `ADC_GAIN_DB` from the AC gain test before using the PSRR result.

### PSRR- (`tb_psrrn.sp`)

The positive rail is held at DC and a 1 V AC perturbation is injected on `vss`:

```spice
VAC_NEG vss 0 DC 0 AC 1
```

The deck measures output response to negative-supply ripple and computes:

```spice
PSRR_MINUS_DB = ADC_GAIN_DB - APS_MINUS_DB
```

Set `ADC_GAIN_DB` from the AC gain test before using the PSRR result.

### Slew Rate (`tb_sr.sp`)

The OTA is configured as a unity-gain buffer. The input uses a PWL waveform that steps from `VICMR_MIN` to `VICMR_MAX`, holds, then steps back down:

```spice
V_IN_POS vip 0 PWL(...)
XU1 vip vout vout vdd vss ibias vb2 DUT_UNIVERSAL
```

The deck measures the output transition time between 10% and 90% thresholds:

```spice
SR_POS_Vus = (V_TH_90_R - V_TH_10_R) / (T_90_R - T_10_R) * 1e-6
SR_NEG_Vus = abs((V_TH_90_F - V_TH_10_F) / (T_90_F - T_10_F)) * 1e-6
```

The reported units are V/us. Update `VICMR_MIN`, `VICMR_MAX`, and `UGF_EST` from earlier simulations before running this deck.

### Operating Point (`tb_op.sp`)

The operating-point deck biases the OTA at a fixed common-mode input voltage and runs a dummy DC sweep to force printed output. It is intended for checking device regions, node voltages, currents, and extracted operating-point parameters in the HSPICE listing.

If the simulator reports an unexpected end-of-file error, add a final `.end` statement to the deck.

## Practical Notes

- `tb_cmrr.sp`, `tb_psrrp.sp`, `tb_psrrn.sp`, and `tb_sr.sp` depend on values measured by earlier simulations. Update those parameters instead of relying on placeholder defaults.
- The wrapper does not automatically detect DUT pins. The `DUT_HAS_VB2` value must match the selected DUT netlist.
- The testbenches are written for HSPICE syntax and measurement functions such as `.meas`, `deriv()`, `vm()`, `vp()`, and `vdb()`.
- If include-path errors occur, run the deck from the directory expected by its `.include` statements or adjust the include paths consistently.
