# OTA subcircuit topologies
This directory contains subcircuit topologies used to generate OTA with bias circuits. 

## Directory structure 
- *bias*: contains different low frequency analog bias topologies which provide voltage reference to local generators (15 circuits)
- *local_generation*: contains various local current/voltage biasing used for OTA circuits
- *OTA*: contains OTA signal path topologies
- *merge_OTA.py*: utilizes *bias, local_generation, OTA* subcircuits to generate full OTA circuits with proper biasing
