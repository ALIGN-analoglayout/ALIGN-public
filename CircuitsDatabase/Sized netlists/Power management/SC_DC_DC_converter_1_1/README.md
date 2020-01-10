## 1:1 series parallel SC DC DC Converter

### Circuit Description

The SC DC DC converter is a 1:1 converter that in this testbench converts a voltage of 1 V to about 0.85 V

### Pin description

* Vin - input common mode DC + input AC
* Vout - output node connected to a load resistor and capacitor
* phi1 - clock signal
* phi2 - clock signal

Phi1 and phi2 are non-overlapping clock signals

### Initial setup + Testbench

The initial setup, for the voltages and currents to these input pins, and the testbench are present in the spice file.

This design has a 200 pF flying capacitor and operates at a frequency of 200 MHz

Simulations
* Transient - efficiency of the converter 

### Performance Metrics

* Conduction loss + Parasitic loss - 567 uW
* Switching loss - 0.52 uW
* Output voltage - 0.85 V
* Output current - 3.77 mA
* Efficiency - 85 %

### Constraints

* Routing parasitics are very critical in this circuit and need to be minimized
