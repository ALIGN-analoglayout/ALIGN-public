#Simple tutorial on package python using setuptools.

To run the test in a container:
````
tar cvf - . | docker run -i --rm --mount source=funniestVol,target=/vol ubuntu bash -c "cd /vol; tar xvf -"
docker run --rm --mount source=funniestVol,target=/vol -it with_python_protobuf bash -c "export https_proxy=http://proxy-chain.intel.com:911; source /sympy/bin/activate; cd /vol; python setup.py develop; python setup.py test"
````
