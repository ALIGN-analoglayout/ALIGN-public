# Detailed Router (binary only for now)

You'll want to get an account at hub.docker.com.
Send steven.m.burns@intel.com an email with your docker user name and you'll get access to this dockerimage.

It is named: darpaalign/detailed_router

To build it (if you have access to the two tarballs with the binaries in them):
````bash
docker build -f Dockerfile.build -t darpaalign/detailed_router .
````
# Collateral

The following will run collateral generation for the three strawman processes:
````
(cd DR_COLLATERAL_Generator/strawman1 && python3 ../gen.py)
(cd DR_COLLATERAL_Generator/strawman2 && python3 ../gen.py)
(cd DR_COLLATERAL_Generator/strawman3 && python3 ../gen.py)
(cd DR_COLLATERAL_Generator/strawman1_ota && python3 ../gen.py)
(cd DR_COLLATERAL_Generator/strawman2_ota && python3 ../gen.py)
(cd DR_COLLATERAL_Generator/strawman3_ota && python3 ../gen.py)
````
