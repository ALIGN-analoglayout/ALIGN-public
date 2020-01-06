## Fully differential Telescopic OTA

### Circuit Description

This OTA (Operational Transconductance Amplifier) circuit is used to achieve good gain and comparably higher output swing.

The diagram of the circuit is as follows.

![Circuit diagram](schematic.PNG)

The circuit contains a continous time common mode feedback loop.

### Pin description

* Vin - input common mode DC + input AC
* Voutp - output of the amplifier
* Voutn - output of the amplifier
* id - bias current input to tail current mirror
* Vdd - supply voltage
* Bias voltages

### Initial setup + Testbench

The initial setup, for the voltages and currents to these input pins, and the testbench is present in the spice file.

Simulations
* DC - operating point information
* AC - gain, three dB frequency, unity gain frequency, phase margin

The AC response plot is shown below

![AC response](AC_response.png)

### Performance Metrics

* Gain - 36 dB
* Three dB frequency - 13 MHz
* Unity gain frequency - 454 MHz
* Phase margin ~ 80 degrees

### Constraints

* The input differential pair in the schematic needs to be matched
* The current mirrors shown in the schematic need to be matched
