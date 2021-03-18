# Introduction

The align.schema module attempts to formalize specification & communication of schematic and layout information used in various stages of the ALIGN toolkit.

While the classes and methods implemented in this module can also be used as a Domain Specific Language (DSL) for analog circuit representation, this is not our target goal at the current point in time.

## Data representation
Almost all the attributes for our API can be easily interpreted by simply viewing the type hints in our class definitions. This document instead focuses on how these classes may be used using concrete examples. Please view tests/schema for additional examples.

A couple of important things to note:
1. All the classes do a certain level of data validation. Some of the classes might additionally do a certain level of casting. Parameter values are a unique example of this. Whether you provide int, float or string, the values will get converted to python strings for internal storage. Remember the type hints in our implementation refer to what the programmer should expect the type to be after an object has already been loaded in. It says nothing about the user input.
2. Nearly all attributes get converted to upper-case internally. The simple reason behind this is that SPICE is case-insensitive. The most notable exception to this rule are the commands under align.schema.constraints which are parsed as python expressions and are hence case sensitive.

With that said, let us get started!

## Create a SPICE MODEL

There are essentially two types of SPICE models:
1. Elementary models (RES, CAP, IND, PMOS, NMOS etc.) which come pre-defined by a given simulator
2. Derived models (.MODEL statements in SPICE) which are usually declared by the PDK

Both of these are handled in align.schema using a single Model class:
```python
class Model(schema.BaseModel):
    name : str                 # Model Name
    base : Optional[Model]     # Model Base (for derived models)
    pins : Optional[List[str]] # List of pin names (derived from base if base exists)
    parameters : Optional[Dict[str, str]]   # Parameter Name: Value mapping (inherits & adds to base if needed)
    prefix : Optional[str]     # Instance name prefix, optional
```

The usage will differ slightly depending upon the type of model we wish to declare.

For elementary models:
```python
testmos = Model(
    name = 'TESTMOS',
    pins = ['D', 'G', 'S', 'B'],
    parameters = {'PARAM1': '1.0', 'PARAM2': '2'}
    )
```
Note the absence of the 'base' argument above.

For derivative models:
```python
MyDevice = Model(
    name='MyDevice',
    base=testmos,
    parameters={'PARAM1': '3'}
    )
```
Note the absence of the 'pins' argument above.

The above statement is motivated by the SPICE statement:
```spice
.MODEL NEWMOS TESTMOS PARAM3=3
```
However, since parameters hold a lot of importance in the ALIGN flow, we find it easier to copy over parameter values to the inherited model instead of just providing a pointer. So the above model if dumped out from align.schema.Model will look something like:
```spice
.MODEL NEWMOS TESTMOS PARAM1=1.0 PARAM2=2 PARAM3=3
```

## Instantiate a device

Now that we have a model available to us, we can instantiate a device.

```python
M1 = Instance(
        name='M1',
        model=testmos,
        pins={'D': 'NET01', 'G': 'NET02', 'S': 'NET03', 'B': 'NET04'},
        parameters={'PARAM1':'NF*4'}
    )

```

## Create a subcircuit

```python
subckt = SubCircuit(
    name = 'leaf_subckt',
    pins = ['PIN1', 'PIN2'],
    parameters = {'PARAM1':'1', 'PARAM2':'1E-3'})
subckt.add(M1)
```

## Tying it all together

```python
# Declare a new three terminal model
ThreeTerminalDevice = Model(
    name='ThreeTerminalDevice',
    pins=['A', 'B', 'C'],
    parameters={'MYPARAMETER': '1'})

# Create leaf level subcircuit 2 transistors
leaf_subckt = SubCircuit(
    name='leaf_subckt',
    pins=['PIN1', 'PIN2', 'PIN3'],
    parameters={'MYPARAMETER':'1'})
leaf_subckt.add(
    Instance(
        name='M1',
        model=testmos,
        pins={'D': 'PIN3', 'G': 'PIN1', 'S': 'PIN1', 'B': '0'},
        parameters={'PARAM1':'NF*4'}))
leaf_subckt.add(
    Instance(
        name='M2',
        model=testmos,
        pins={'D': 'PIN3', 'G': 'PIN1', 'S': 'PIN2', 'B': '0'},
        parameters={'PARAM1':'NF*4'}))

# Create intermediate level subcircuit with 1 transistor & 1 leaf_subckt
intermediate_subckt = SubCircuit(
    name='intermediate_subckt',
    pins=['PIN1', 'PIN2'])
intermediate_subckt.add(
    Instance( name='I1',
              model=leaf_subckt,
              pins={'PIN1': 'PIN1', 'PIN2': 'PIN2', 'PIN3': 'NET1'},
              parameters= {'MYPARAMETER':'2'}))
intermediate_subckt.add(
    Instance( name='I2',
              model=leaf_subckt,
              pins={'PIN1': 'PIN1', 'PIN2': 'PIN2', 'PIN3': 'NET2'},
              parameters= {'MYPARAMETER':'2'}))
intermediate_subckt.add(
    Instance(
        name='M1',
        model=testmos,
        pins={'D': 'NET1', 'G': 'PIN1', 'S': 'PIN2', 'B': '0'},
        parameters={'PARAM1':'NF*4'}
    )

# Create top level netlist with 1 intermediate level & 1 leaf level subckt
ckt = Circuit()
ckt.add(Instance(
    name='XSUB1',
    model=intermediate_subckt,
    pins={'PIN1':'NET1', 'PIN2': 'NET2'}))
ckt.add(Instance(
    name='XSUB2',
    model=leaf_subckt,
    pins={'PIN1': 'NET1', 'PIN2': 'NET2', 'PIN3': 'NET3'},
    parameters={'MYPARAMETER': '3'}))
```