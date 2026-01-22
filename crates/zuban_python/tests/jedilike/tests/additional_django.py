from django.db import models

class CustomField[T1, T2](models.CharField[T1, T2]):
    pass

class BusinessModel(models.Model):
    custom_field = CustomField()

def f(inst: BusinessModel):
    #? str()
    inst.custom_field
