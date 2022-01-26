## PDK Abstraction ##
__models.sp__ (Model library can be defined in a Python script and serialized to the file below for human readability)
```
.model n nmos nfin=1 w=1 nf=1 l=1 m=1
.model p nmos nfin=1 w=1 nf=1 l=1 m=1
```

__templates.sp__ (Template library can be defined in a Python script and serialized to the file below for human readability)
```
.subckt nmos d g s b
* [{"constraint": "Generator", "_generator": "mos"}]
m0 d g s b nmos
.ends

.subckt dp_n da db ga gb s b
* [{"constraint": "Generator", "_generator": "mos", "_matched_params": True}]
m0 da ga s b nmos
m1 db gb s b nmos
.ends

.subckt scm_p da db s
* [{"constraint": "Generator", "_generator": "mos", "_matched_params": True}]
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
```

## ALIGN Input ##
__netlist.sp__
```
.subckt ota_five vccx vssx von vin vip vb
mn0 vxx vx vssx vssx n nf=2 m=8    // this is an additional device just for demonstration
mn1 vcm vb vssx vssx n nf=2 m=8
mn2 von vip vcm vssx n nf=2 m=16
mn3 vop vin vcm vssx n nf=2 m=16
mp4 vop vop vccx vccx p nf=2 m=4
mp5 von vop vccx vccx p nf=2 m=4
.ends ota_five
```

## ALIGN Execution ##
__phase=0__ (parse netlist)
```python
# Hierarchy
[
    {"name": "ota_five", "pins": ["vccx", "vssx", "von", "vin", "vip", "vb"],
        "constraints": [...],
        "elements": [
            {"name": "mn0", "model": "n", "fa_map":{"d": "vxx", "g": "vx", "s": "vssx", "b": "vssx"}, "parameters": {...} 
            {"name": "mn1", "model": "n", ...},
            {"name": "mn2", "model": "n", ...},
            {"name": "mn3", "model": "n", ...},
            {"name": "mp4", "model": "p", ...},
            {"name": "mp5", "model": "p", ...}
        ]
    }
]
```

__phase=1__ (after compiler transformations, template and generator identification. note that both mn0 and mn1 mapped to nmos_1)
```python
# Hierarchy
[
    {"name": "ota_five", "pins": [...],
        "constraints": [],
        "elements": [
            {"name": "mn0", "model":"nmos_1", "fa_map":{"d": "vxx", "g": "vx", "s": "vssx", "b": "vssx"},
                "constraints": [{"constraint": "Generator", "_generator": "mos"}, {"<additional constraints per mn0>"}]},
            {"name": "mn1", "model":"nmos_1", "fa_map":{...},
                "constraints": [{"constraint": "Generator", "_generator": "mos"}, {"<additional constraints per mn1>"}]},
            {"name": "dp_n_1_i1", "model":"dp_n_1", "fa_map":{...},
                "constraints": [{"constraint": "Generator", "_generator": "mos"}, {"<additional constraints per instance>"}]},
            {"name": "scm_p_1_i1", "model":"scm_p_1", "fa_map":{...},
                "constraints": [{"constraint": "Generator", "_generator": "mos", "_matched_params": True}, {"<additional constraints per instance>"}]}
        ]
    },
    {"name": "nmos_1", "pins": ["d", "g", "s", "b"],
        "elements": [
            {"name": "mn0", "model":"n", "fa_map":{"d": "d", "g": "g", "s": "s", "b": "b"}, "parameters": {<ota_five.mn1==ota_five.mn0>} },
        ]
    },
    {"name": "dp_n_1", "pins": ["da", "db", "ga", "gb", "s", "b"],
        "elements": [
            {"name": "mn0", "model":"n", "fa_map":{"d": "da", "g": "ga", "s": "s", "b": "b"}, "parameters": {<ota_five.mn2>} },
            {"name": "mn1", "model":"n", "fa_map":{"d": "db", "g": "gb", "s": "s", "b": "b"}, "parameters": {<ota_five.mn3>} },
        ]
    },
    {"name": "scm_p_1", "pins": ["da", "db", "s"],
        "elements": [
            {"name": "mp0", "model":"p", "fa_map":{...}, "parameters": {<ota_five.mp4>} },
            {"name": "mp1", "model":"p", "fa_map":{...}, "parameters": {<ota_five.mp5>} },
        ]
    }
]
```

Call mos with the subcircuit object (e.g. nmos_1) and constraints per instance. mos returns an abstract name and dictionary of concrete name for each one.

__phase=2__ (after primitive generation, before placement)
```python
# Hierarchy
[
    {"name": "ota_five", "pins": ["vccx", "vssx", "von", "vin", "vip", "vb"],
        "constraints": [],
        "elements": [
            {"name": "mn0", "model":"nmos_1", "fa_map":{"d": "vxx", "g": "vx", "s": "vssx", "b": "vssx"},
                "constraints": [...],
                "abstract_name": "<guid1>"},
            {"name": "mn1", "model":"nmos_1", "fa_map":{...},
                "constraints": [...],
                "abstract_name": "<guid1 if constraints match, else guid2>",
            {"name": "i_dp_n_1", "model":"dp_n_1", "fa_map":{"da": "von", "db": "vop", "ga": "vip", "gb": "vin", "s": "vcm"},
                "constraints": [...],
                "abstract_name": "<guid3>"},
            {"name": "i_scm_p_1", "model":"scm_p_1", "fa_map":{...},
                "constraints": [...],
                "abstract_name": "<guid4>"}
        ]
    }
]
# A separate data structure to store rectangles w/o duplication 
{
    "<abstract_name>": {"<concrete_name>": {"bbox":[], "terminals":[], "metadata":[]}}
    "guid1": {"guid1_1": {"bbox":[], "terminals":[], "metadata":[]}},
    "guid1": {"guid1_2": {"bbox":[], "terminals":[], "metadata":[]}},
    ...
}
```

__phase=3__ (a variant after placement, before routing)
```python
# Hierarchy
[
    {"name": "ota_five", "pins": [...], 
        "constraints": [],
        "concrete_name": "ota_five_0",
        "elements": [
            {"name": "mn0", "model":"nmos_1", "fa_map":{"<might differ w/ partial routing>"},
                "constraints": [...],
                "abstract_name": "<guid1>", 
                "concrete_name": "<guid11>"},
            {"name": "mn1", "model":"nmos_1", "fa_map":{...},
                "constraints": [...],
                "abstract_name": "<guid1/guid2>",
                "concrete_name": "<guid11/guid12>"},
            {"name": "i_dp_n_1", "model":"dp_n_1", "fa_map":{...},
                "constraints": [...],
                "abstract_name": "<guid3>",
                "concrete_name": "<guid31>"},
            {"name": "i_scm_p_1", "model":"scm_p_1", "fa_map":{...},
                "constraints": [...],
                "abstract_name": "<guid4>",
                "concrete_name": "<guid41>"
            }
        ]
    }
]
# A separate data structure to store rectangles w/o duplication 
{
    "<abstract_name>": {"<concrete_name>": {"bbox":[], "terminals":[], "metadata":[]}}
    "guid1": {"guid1_1": {"bbox":[], "terminals":[], "metadata":[]}},
    "guid1": {"guid1_2": {"bbox":[], "terminals":[], "metadata":[]}}, ...
}
```

__phase=4__ (a variant after routing)
```python
[
    {"name": "ota_five", "pins": [...], 
        "concrete_name": "ota_five_0",
        "elements": [
            {"name": "mn0", "model":"nmos_1", "fa_map":{"<might differ w/ partial routing>"},
                "constraints": [...],
                "abstract_name": "<guid1>", 
                "concrete_name": "<guid11>",
                "transformation": {}},
            {"name": "mn1", "model":"nmos_1", "fa_map":{...},
                "constraints": [...],
                "abstract_name": "<guid1/guid2>", 
                "concrete_name": "<guid11/guid21>",
                "transformation": {}},
            {"name": "i_dp_n_1", "model":"dp_n_1", "fa_map":{...},
                "constraints": [...],
                "abstract_name": "<guid3>", 
                "concrete_name": "<guid31>",
                "transformation": {}},
            {"name": "i_scm_p_1", "model":"scm_p_1", "fa_map":{...},
                "constraints": [...],
                "abstract_name": "<guid4>", 
                "concrete_name": "<guid41>",
                "transformation": {}}
        ]
    }
]
# A separate data structure to store rectangles w/o duplication 
{
    "<abstract_name>": {"<concrete_name>": {"bbox":[], "terminals":[], "metadata":[]}}
    "guid1": {"guid1_1": {"bbox":[], "terminals":[], "metadata":[]}},
    "guid1": {"guid1_2": {"bbox":[], "terminals":[], "metadata":[]}},
    "ota_five": {"ota_five_0": {"bbox":[], "terminals":["<new terminals from router>"], "metadata":[]}}, ...
}
```
