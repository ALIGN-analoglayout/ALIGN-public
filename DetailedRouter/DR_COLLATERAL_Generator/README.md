# Generator for Strawman Detailed Router Collateral

The python script gen.py will construct the following files (needed for the detailed router) from Process.json (which you specify with the -tf options.).

arch.txt - specifies the global routing grid in terms of poly pitches (x direction) and fin pitches (y direction)

design_rules.txt - specifies the end-to-end and minimum length rules for each metal layer

car_generators.txt - specifies the via extensions (can be regenerated using gen_car.py)

layers.txt - specifies the layer stack and connectivity (also the poly and fin pitches)

There are three strawman process versions currently:

1) The rule set is very simple. All metals have the same pitch (72nm). The poly and fin pitches are also the same. The wire widths are 40nm and the space between wires is 32nm. Metal end to end is also 72nm and min length should be three times that.

3) Same as 1) except for metals 4 and 5 where the width and space bump up to 60nm and 48nm. (Enclosure extensions for all layers are still 16nm.)

3) Same as 2) except for metals 4 and 5 where the width and space bump up to 80nm and 64nm.

