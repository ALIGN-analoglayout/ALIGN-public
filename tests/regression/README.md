# Running regression Tests

To run all the design in examples through the flow, you can do the following:
- Set the environment variables `$ALIGN_HOME` and `$ALIGN_WORK_DIR`.
- Then run the regression tagged tests
```python
cd $ALIGN_HOME
pytest -vv --runregression -- tests/regression
```

Some of these tests take a long time. This will remove the two longest running (currently) tests:
```python
cd $ALIGN_HOME
pytest -vv --runregression -k 'not SAR_ADC_6b_2GSPS and not vco and not sc_dc_dc_converter' -- tests/regression
```
