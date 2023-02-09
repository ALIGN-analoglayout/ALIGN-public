# A MockPDK inspired by 65nm bulk technology

The abstraction details are provided in the presentation [PDK_Abstraction_guide](https://github.com/ALIGN-analoglayout/ALIGN-public/blob/documentation_update/pdks/PDK_Abstraction_Guide.pptx).

## Key files

* layers.json: Design rules such as metal width and pitch are defined in this file.
* models.sp and [library.py](https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/align/schema/library.py): A library of device definitions in SPICE file.
* gen_param.py: Method to convert device SPICE parameters to layout parameters.
* mos.py, res.py, cap.py, guard_ring.py: Rule-based device generators.
* Align_primitives.py, fabric_Res.py, fabric_Cap.py: Python utilities for standalone usage of device generators. 

## References
