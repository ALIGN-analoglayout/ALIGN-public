# Strawman Detailed Router Collateral

This directory contains an example rule set (very simple now) for the detailed router.

arch.txt - specifies the global routing grid in terms of poly pitches (x direction) and fin pitches (y direction)

design_rules.txt - specifies the end-to-end and minimum length rules for each metal layer

car_generators.txt - specifies the via extensions (can be regenerated using gen_car.py)

layers.txt - specifies the layer stack and connectivity (also the poly and fin pitches)

metal_templates.txt - specifies the metal templates for each layer.

The rule set is very simple. All metals have the same pitch (72nm). The poly and fin pitches are also the same. The wire widths are 40nm an the space between wires is 32nm.
