## Telescopic OTA - single ended and stacked

### Circuit Description

This OTA (Operational Transconductance Amplifier) circuit is used to achieve high gain and comparably higher output swing.

### Pin description

* Vin - input common mode DC + input AC
* Vout - output of the amplifier
* Id - bias current input

### Initial setup + Testbench

The initial setup, for the voltages and currents to these input pins, and the testbench is present in the spice file.

Simulations
* DC - operating point information
* AC - gain, three dB frequency, unity gain frequency, phase margin

### Performance Metrics

* Current - 157 uA
* Gain - 52 dB
* Unity gain frequency - 966 MHz
* 3-dB frequency - 2.42 MHz
* Phase margin ~ 88 degrees

### Constraints

* The input differential pair in the schematic needs to be matched
* The current mirrors shown in the schematic need to be matched
