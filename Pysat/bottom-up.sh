#!/bin/bash

for i in dp1x dp2x dp4x mirrors
do
    ./flow-${i}.sh | tee -a ${i}.log
done

#
# Copy stack
#
(cd INPUT && tar cvf - stack_global_router_out.json stack_placer_out_scaled.json) | docker run --rm --mount source=equalizerInputVol,target=/INPUT -i ubuntu /bin/bash -c "cd /INPUT && tar xvf -"

for i in ctle wcap comp diff lane top
do
    ./flow-${i}.sh --script ${i}.py | tee -a ${i}.log
done

python errors.py dp1x dp2x dp4x mirrors ctle wcap comp diff lane top > bottom-up.test_result

	 






