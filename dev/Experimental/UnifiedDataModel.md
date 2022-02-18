## PDK Module ##
__models.sp__ (Model library can be defined in a Python script and serialized to the file below for human readability. nmos/pmos/res are universal base models that can be customized per technology)
```
.model n nmos nfin=1 w=1 nf=1 l=1 m=1
.model p nmos nfin=1 w=1 nf=1 l=1 m=1
.model tfr res w=1 l=1
```
__templates.sp__ library can be defined in a Python script and serialized to the file below for human readability)
```
.subckt nmos d g s b
* @: Generator(name="mos")
m0 d g s b nmos
.ends

.subckt dp_n da db ga gb s b
* @: Generator(name="mos")
* @: SymmetricBlocks(pairs=[['m0','m1']], direction='V')
m0 da ga s b nmos
m1 db gb s b nmos
.ends

.subckt scm_p da db s
* @: Generator(name="mos")
m0 da da s s pmos
m1 db da s s pmos
.ends

.subckt cm3_n da db dc s
m0 da da s s nmos
m1 db da s s nmos
m2 dc da s s nmos
.ends

.subckt inv i o vcc vss
m0 o i vcc vcc pmos
m1 o i vss vss nmos
.ends

.subckt ota_five <pins> 
* @: Generator(name="ota")
< instances >
.ends

```

__init.py__  generators that are exposed to ALIGN
```python
from module_one import mos  # mos keyword is specified in Generator directive
from module_two import res  # res is the base model for tfr
from module_ota import ota  # ota keyword is specified in Generator directive
```

## ALIGN Input ##
__netlist.sp__
```
.subckt ota_five vccx vssx von vin vip vb
mn0 vxx vx vssx vssx n nf=2 m=8
mn1 vcm vb vssx vssx n nf=2 m=8
mn2 von vip vcm vssx n nf=2 m=16
mn3 vop vin vcm vssx n nf=2 m=16
mp4 vop vop vccx vccx p nf=2 m=4
mp5 von vop vccx vccx p nf=2 m=4
.ends ota_five
```

__netlist.const.json__
```python
[
    {"constraint": "Generator", "instances": "mn0", "parameters":[{"key": "value0"}]},
    {"constraint": "Generator", "instances": "mn1", "parameters":[{"key": "value1"}]}
]
```

## ALIGN Execution ##
__phase=0__ (Just after netlist parsing)
```python
# Hierarchy
[
    {
        "name": "ota_five",
        "pins": ["vccx", "vssx", "von", "vin", "vip", "vb"],
        "constraints": [
            {"constraint": "Generator", "instances": "mn0", "parameters":[{"key": "n_rows", "value": "1"}]},
            {"constraint": "Generator", "instances": "mn1", "parameters":[{"key": "n_rows", "value": "2"}]}
        ],
        "instances": [
            {"name": "mn0", "model": "n", "fa_map":[{"formal": "d", "actual": "vxx"}, ...], "parameters": [{"nf": "2", "m": "8"}]},
            {"name": "mn1", "model": "n", ...},
            {"name": "mn2", "model": "n", ...},
            {"name": "mn3", "model": "n", ...},
            {"name": "mp4", "model": "p", ...},
            {"name": "mp5", "model": "p", ...}
        ]
    }
]
```
__phase=1__ (After compiler transformations: e.g., template and generator identification. Just before primitive generation.)
```python
# Hierarchy
[
    {
        "name": "ota_five",
        "pins": [...],
        "constraints": [], # Generator constraints are pushed to subcircuits. Okay to keep here for diagnostics.
        "instances": [
            {"name": "mn0",     "model": "guid1", "fa_map": [...]},
            {"name": "mn1",     "model": "guid2", "fa_map": [...]},
            {"name": "mn2_mn3", "model": "guid3", "fa_map": [...]}},
            {"name": "mp4_mp5", "model": "guid4", "fa_map": [...]}},
        ]
    },
    {
        "name": "guid1",
        "pins": ["d", "g", "s", "b"],  # pins identified by querying the model or PDK template definiton
        "constraints": [{"constraint": "Generator", "name": "mos", "instances": "m0", "parameters":[...]}],
        "instances": [{"name": "m0", "model":"n", "fa_map": [...], "parameters": [<params of mn0>]}]
    },
    {
        "name": "guid2",
        "pins": ["d", "g", "s", "b"],
        "constraints": [{"constraint": "Generator", "name": "mos", "instances": "m0", "parameters":[...]}],
        "instances": [{"name": "m0", "model":"n", "fa_map": [...], "parameters": [<params of mn1>]}]
    },
    {
        "name": "guid3",
        "pins": ["da", "db", "ga", "gb", "s", "b"],
        "constraints": [<from the PDK template definiton and user>],
        "instances": [
            {"name": "m0", "model":"n", "fa_map":{"d": "da", "g": "ga", "s": "s", "b": "b"}, "parameters": [<params of mn2>]},
            {"name": "m1", "model":"n", "fa_map":{"d": "db", "g": "gb", "s": "s", "b": "b"}, "parameters": [<params of mn3>]}
        ]
    },
    {
        "name": "guid4",
        "pins": ["da", "db", "s"],  
        "constraints": [<from the PDK template definiton and user>],
        "instances": [
            {"name": "m0", "model":"p", "fa_map":{...}, "parameters": [<params of mp4>]},
            {"name": "m1", "model":"p", "fa_map":{...}, "parameters": [<params of mp5>]}
        ]
    }
]
```

ALIGN calls the annotated generators from PDK to create primitives (no hard coded model names).

__phase=2__ (After primitive generation, before placement. Suppose max 2 variants.)
```python
# Hierarchy
[
    {
        "name": "ota_five",
        "pins": [...],
        "constraints": [
            {"constraint": "Generator", "instances": "mn0", "parameters":{<param1>}},
            {"constraint": "Generator", "instances": "mn1", "parameters":{<param2>}}
        ],
        "instances": [
            {"name": "mn0", "model": "guid1", "fa_map": [...]},
            {"name": "mn1", "model": "guid2", "fa_map": [...]},
            {"name": "mn2_mn3", "model": "guid3", "fa_map": [...]},
            {"name": "mp4_mp5", "model": "guid4", "fa_map": [...]},
        ]
    },
    {
        "name": "guid1",
        "pins": ["d", "g", "s", "b"],
        "constraints": [{"constraint": "Generator", "name": "mos", "instances": "m0", "parameters": [<param1>]}],
        "instances": [{"name": "m0", "model":"n", "fa_map": [...], "parameters": [<params of mn0>]}],
        "concrete_name": "guid1_1", "bbox":[], "terminals":[], "metadata":[...]
    },
    {
        "name": "guid2",
        "pins": ["d", "g", "s", "b"],
        "constraints": [{"constraint": "Generator", "name": "mos", "instances": "m0", "parameters":[<param2>]}],
        "instances": [{"name": "m0", "model":"n", "fa_map": [...], "parameters": [<params of mn1>]}],
        "concrete_name": "guid2_1", "bbox":[], "terminals":[], "metadata":[...]
    },
    {
        "name": "guid3",
        "pins": ["da", "db", "ga", "gb", "s", "b"],
        "constraints": [{"constraint": "Generator", "name": "mos",...}],
        "instances": [
            {"name": "m0", "model":"n", "fa_map":{"d": "da", "g": "ga", "s": "s", "b": "b"}, "parameters": [<params of mn2>]},
            {"name": "m1", "model":"n", "fa_map":{"d": "db", "g": "gb", "s": "s", "b": "b"}, "parameters": [<params of mn3>]}
        ],
        "concrete_name": "guid3_1", "bbox":[], "terminals":[], "metadata":[...]
    },
    {
        "name": "guid3",
        "pins": ["da", "db", "ga", "gb", "s", "b"],
        "constraints": [{"constraint": "Generator", "name": "mos",...}],
        "instances": [
            {"name": "m0", "model":"n", "fa_map":{"d": "da", "g": "ga", "s": "s", "b": "b"}, "parameters": [<params of mn2>]},
            {"name": "m1", "model":"n", "fa_map":{"d": "db", "g": "gb", "s": "s", "b": "b"}, "parameters": [<params of mn3>]}
        ],
        "concrete_name": "guid3_2", "bbox":[], "terminals":[], "metadata":[...]
    },
    {
        "name": "guid4",
        "pins": ["da", "db", "s"],
        "constraints": [{"constraint": "Generator", "name": "mos",...}],
        "instances": [
            {"name": "m0", "model":"p", "fa_map":{...}, "parameters": [<params of mp4>]},
            {"name": "m1", "model":"p", "fa_map":{...}, "parameters": [<params of mp5>]}
        ],
        "concrete_name": "guid4_1", "bbox":[], "terminals":[], "metadata":[...]
    },
    {
        "name": "guid4",
        "pins": ["da", "db", "s"],
        "constraints": [{"constraint": "Generator", "name": "mos",...}],
        "instances": [
            {"name": "m0", "model":"p", "fa_map":{...}, "parameters": [<params of mp4>]},
            {"name": "m1", "model":"p", "fa_map":{...}, "parameters": [<params of mp5>]}
        ],
        "concrete_name": "guid4_2", "bbox":[], "terminals":[], "metadata":[...]
    }
```

__phase=3__ (A variant after placement)
```python
# Hierarchy
[
    {
        "name": "ota_five",
        "pins": [...],
        "constraints": [],
        "instances": [
            {"name": "mn0", "model": "guid1", "fa_map": [...], "transformation":[...], "concrete_name": "guid1_1"},
            {"name": "mn1", "model": "guid2", "fa_map": [...], "transformation":[...], "concrete_name": "guid2_1"},
            {"name": "mn2_mn3", "model": "guid3", "fa_map": [...], "transformation":[...], "concrete_name": "guid3_1"},
            {"name": "mp4_mp5", "model": "guid4", "fa_map": [...], "transformation":[...], "concrete_name": "guid4_2"},
        ],
        "concrete_name": "ota_five_0",
        "bbox":[]
    },
    ...
```

__phase=4__ (A variant after global routing)
```python
# Hierarchy
[
    {
        "name": "ota_five",
        "pins": [...],
        "constraints": [
            {"constraint": "Generator", "instances": "mn0", "parameters":{<param1>}},
            {"constraint": "Generator", "instances": "mn1", "parameters":{<param2>}}
        ],
        "instances": [
            {"name": "mn0", "model": "guid1", "fa_map": [...], "transformation":[...], "concrete_name": "guid1_1"},
            {"name": "mn1", "model": "guid2", "fa_map": [...], "transformation":[...], "concrete_name": "guid2_1"},
            {"name": "mn2_mn3", "model": "guid3", "fa_map": [...], "transformation":[...], "concrete_name": "guid3_1"},
            {"name": "mp4_mp5", "model": "guid4", "fa_map": [...], "transformation":[...], "concrete_name": "guid4_2"},
        ],
        "concrete_name": "ota_five_0",
        "bbox":[],
        "global_routes":[]
    },
    ...
```

__phase=5__ (A variant after detailed routing)
```python
# Hierarchy
[
    {
        "name": "ota_five",
        "pins": [...],
        "constraints": [
            {"constraint": "Generator", "instances": "mn0", "parameters":{<param1>}},
            {"constraint": "Generator", "instances": "mn1", "parameters":{<param2>}}
        ],
        "instances": [
            {"name": "mn0", "model": "guid1", "fa_map": [...], "transformation":[...], "concrete_name": "guid1_1"},
            {"name": "mn1", "model": "guid2", "fa_map": [...], "transformation":[...], "concrete_name": "guid2_1"},
            {"name": "mn2_mn3", "model": "guid3", "fa_map": [...], "transformation":[...], "concrete_name": "guid3_1"},
            {"name": "mp4_mp5", "model": "guid4", "fa_map": [...], "transformation":[...], "concrete_name": "guid4_2"},
        ],
        "concrete_name": "ota_five_0",
        "bbox":[],
        "global_routes":[],
        "terminals": []
    },
    ...
```
