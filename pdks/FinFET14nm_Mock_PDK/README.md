# A MockPDK inspired by advanced FinFET processes

The abstraction details are provided in the presentation [FinFET_Mock_PDK_Abstraction](https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/pdks/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.ppt).

## Key files

* layers.json: Design rules such as metal width and pitch are defined in this file.
* models.sp and [library.py](https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/align/schema/library.py): A library of device definitions in SPICE file.
* gen_param.py: Method to convert device SPICE parameters to layout parameters.
* mos.py, res.py, cap.py, guard_ring.py: Rule-based device generators.
* Align_primitives.py, fabric_Res.py, fabric_Cap.py, fabric_ring.py: Python utilities for standalone usage of device generators. 

## References

[1] C. H. Lin et al., "High performance 14nm SOI FinFET CMOS technology with 0.0174 µm2 embedded DRAM and 15 levels of Cu metallization," In IEEE International Electron Devices Meeting, 2014, pp. 3-8.

[2] https://fuse.wikichip.org/news/956/globalfoundries-14hp-process-a-marriage-of-two-technologies/3/

[3] J. Singh et al., "14-nm FinFET technology for analog and RF applications," IEEE Transactions on Electron Devices, vol. 65, no. 1, pp. 31-37, 2018.

[4] https://en.wikichip.org/wiki/14_nm_lithography_process#GlobalFoundries

