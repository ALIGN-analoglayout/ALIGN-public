### Placer Crash

To reproduce the second cascode_current_mirror_ota bug:

```bash
../PlaceRouteHierFlow/pnr_compiler placer_crash2/ cascode_current_mirror_ota.{lef,v,map} FinFET_Mock_PDK_Abstraction.json cascode_current_mirror_ota 1 0 > LOG2
```

To reproduce the telescope_ota bug (pin misalignment):

```bash
../PlaceRouteHierFlow/pnr_compiler telescopic_ota/ telescopic_ota.{lef,v,map} FinFET_Mock_PDK_Abstraction.json telescopic_ota 1 0 > telescopic_ota.log
```

To reproduce current_mirror_ota bug (PnR crash):

```bash
../PlaceRouteHierFlow/pnr_compiler current_mirror_ota/ current_mirror_ota.{lef,v,map} FinFET_Mock_PDK_Abstraction.json current_mirror_ota 1 0 > current_mirror_ota.log
```
To reproduce a crash in the bug/drc_bug branch (PnR crash):

```bash
../PlaceRouteHierFlow/pnr_compiler switched_capacitor_filter/ switched_capacitor_filter.{lef,v,map} FinFET_Mock_PDK_Abstraction.json switched_capacitor_filter 1 0 > switched_capacitor_filter.log
```
