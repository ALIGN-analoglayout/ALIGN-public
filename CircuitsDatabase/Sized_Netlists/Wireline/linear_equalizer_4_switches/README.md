## Linear equalizer 4 switches

### Circuit Description

The linear equalizer is used to attenuate low-frequency content and amplify high frequency contents. This LE has 4 switches to vary low and high frequency gain.

![Circuit diagram](linear_equalizer_4_switches_schematic.png)

### Pin description

* vin1, vin2 - inputs common mode DC + input AC
* vout1, vout2 - outputs
* vmirror - bias for the current mirror block
* s0, s1, s2, s3 - Switches to vary low and high frequency gain
* vps - supply voltage
* vgnd - ground

### Initial setup + Testbench

The initial setup, for the voltages and currents to these input pins, and the testbench is present in the spice file.

Simulations
* DC - operating point information
* AC - gain, three dB frequency, unity gain frequency, phase margin
* Tran - to check whether output voltage is distorted
