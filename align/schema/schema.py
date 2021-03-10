import pydantic
class BaseModel(pydantic.BaseModel):

    class Config:
        validate_assignment = True
        extra = 'forbid'
        allow_mutation = False
        copy_on_model_validation = False

from pydantic import \
    validator, \
    validate_arguments, \
    PrivateAttr