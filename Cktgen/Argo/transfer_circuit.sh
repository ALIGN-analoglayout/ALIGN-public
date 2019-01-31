kubectl cp $1 load-circuit:/Cktgen/INPUT/cktgen_input.py
echo $1 > desc.txt
kubectl cp desc.txt load-circuit:/Cktgen/INPUT/


