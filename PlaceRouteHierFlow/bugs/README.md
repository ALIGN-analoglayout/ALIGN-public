### Placer Crash

To reproduce second cascode_current_mirror_ota bug:

```bash
../pnr_compiler placer_crash2/ cascode_current_mirror_ota.{lef,v,map} FinFET_Mock_PDK_Abstraction.json cascode_current_mirror_ota 1 0 > LOG2
```

To reproduce telescope_ota bug (pin misalignment):

```bash
../pnr_compiler telescopic_ota/ telescopic_ota.{lef,v,map} FinFET_Mock_PDK_Abstraction.json telescopic_ota 1 0 > telescopic_ota.log
```
