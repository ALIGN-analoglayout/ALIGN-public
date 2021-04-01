from typing import List, Union, Dict, Optional, Tuple
from pydantic import validator, ValidationError, Field
from . import types


class Transistor(types.BaseModel):

    device_type: str
    nf: int

    l: Optional[float]

    w: Optional[float]
    nfin: Optional[int]

    model_name: str

    params: Optional[Dict[str, Union[str, int, float]]]

    @validator('device_type')
    def _validate_device_type(cls, v):
        if v not in ['parallel', 'stack']:
            raise ValueError(f'Device type is either parallel or stack: {v}')
        return v

    @validator('model_name')
    def _validate_model_name(cls, v):
        if v.startswith('n') or v.startswith('p'):
            return v
        else:
            raise ValueError(f'Model name should begin with n or p: {v}')

    @validator('nfin')
    def _validate_width(cls, v, values):
        if v is None and values['w'] is None:
            raise ValueError('Either width or nfin should be specified')
        return v


class TransistorArray(types.BaseModel):

    unit_transistor: Transistor
    m: Dict[int, int]
    ports: Dict[int, Dict[str, str]]
    n_rows: int

    @validator('ports')
    def _validate_ports(cls, v, values):
        if set(v.keys()) != set(values['m'].keys()):
            raise ValueError('Number of devices and ports should match')
        for _, ports in v.items():
            if set(ports.keys()) != {'S', 'D', 'G'} and set(ports.keys()) != {'S', 'D', 'G', 'B'} :
                raise ValueError(f'Missing transistor terminal S/D/G: {ports}')
        return v
