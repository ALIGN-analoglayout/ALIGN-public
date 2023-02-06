# Design-rule-correct analog cell generator
ALIGN uses a cell generator based on a grid methodology that enables
a process-portable DRC and LVS clean analog cell generator. We have validated the cell generator for FinFET as well as bulk-CMOS technologies. To integrate this generator into any new PDK, designers need to modify these PDKs based on corresponding design rules.

## Key highlights

* Multiple layout patterns (common-centroid, interdigitated, and non-common-centroid) and aspect ratios can be generated using this framework. Default is a common-centroid pattern.

* Design rules and connectivity checking are performed within
the cell generator.

* Using the PDK abstraction unit a GDS and a LEF file is
generated for each cell.

## Open-source MockPDKs
We have open-sourced a set of design rules for a MockPDK based
on advanced FinFET process and bulk process. The data used in these PDKs have been generated based on published data in the literature.

 * A MockPDK inspired by advanced FinFET process ([FinFET14nm_Mock_PDK](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/documentation_update/pdks/FinFET14nm_Mock_PDK)).
 * A MockPDK inspired by bulk technologies ([Bulk65nm_Mock_PDK](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/documentation_update/pdks/Bulk65nm_Mock_PDK), [Bulk45nm_Mock_PDK](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/documentation_update/pdks/Bulk45nm_Mock_PDK))
 * A mock PDK inspired by Intel 22nm FinFET Fact Sheet ([finfet](https://github.com/ALIGN-analoglayout/ALIGN-public/tree/documentation_update/align/pdk/finfet)). PDK abstraction contains only Poly, M1-M6 and V1-V5 layers.

 * A MockPDK with non-uniform grid metal grids ([Nonuniform_mock_pdk](https://github.com/ALIGN-analoglayout/ALIGN-public/blob/documentation_update/pdks/Nonuniform_mock_pdk/layers.json)). This PDK is for development and is not functional yet.

