# OTA topologies

There are several operational transconductance amplifier (OTA) topologies that can potentially be used in analog design. 
This repository aims to act as a one-top-shop by compiling various commonly used OTA topolgies compiled from different literature sources into one location.
The OTA topologies in this directory are specified in SPICE netlist format.


## Directory structure

*OTA topologies* repository has the following directory structure:

- *full_OTA* directory contains OTA circuits with proper biasing (1390 variations)
    - *full_differential_OTA*: contains fully differential OTA topologies
    - *single_ended_OTA*: contains single ended OTA topologies
- *generator* directory contains different subcircuits of OTA used to generate the circuits in full_OTA
    - *bias*: contains different low frequency analog bias topologies which provide voltage reference to local generators (15 circuits)
    - *local_generation*: contains various local current/voltage biasing used for OTA circuits
    - *OTA*: contains OTA signal path topologies
    - *merge_OTA.py*: utilizes *bias, local_generation, OTA* subcircuits to generate full OTA circuits with proper biasing
