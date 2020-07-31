file_name=ota_asap7
#file_name=cascode_current_mirror_ota
#file_name=current_mirror_ota
#file_name=strong_arm_latch
#file_name=comparator_3

#export LD_LIBRARY_PATH=/usr/local/lib/lpsolve/lp_solve_5.5.2.5_dev_ux64/
export LP_DIR=/home/grads/l/liyg/master/ALIGN-public/lpsolve
export JSON=/home/grads/l/liyg/master/ALIGN-public/json
export BOOST_LP=/home/grads/l/liyg/master/ALIGN-publict/boost
export GTEST_DIR=/home/grads/l/liyg/master/ALIGN-public/googletest/googletest/
export LD_LIBRARY_PATH=/home/grads/l/liyg/master/ALIGN-public/lpsolve/lp_solve_5.5.2.5_dev_ux64
#scl enable devtoolset-7 bash

lef=.lef
v=.v
map=.map
gds=_gds
source=_0.gds.json
source_file=$file_name$source
target=_0.gds
target_file=$file_name$target
slash=/
target_json=.json

const=.const
const_file=$file_name$const
const_folder=_const
const_folder_file=$file_name$const_folder

source_folder=Results
Feature_value_file=Feature_value
Json_file=$file_name$target_json

lef_file=$file_name$lef
v_file=$file_name$v
map_file=$file_name$map

gds_folder=$file_name$gds

mkdir $gds_folder

source /home/grads/l/liyg/master/ALIGN-public/general/bin/activate

export LD_LIBRARY_PATH=/usr/local/lib/lpsolve/lp_solve_5.5.2.5_dev_ux64/
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/home/yaguang/Desktop/Research/src/tensorflow/bazel-bin/tensorflow

index=0

for i in $(seq 1 1 10000)
do
  index=$((i))
  mkdir $gds_folder$slash$index
  #cp $const_folder_file$slash$index$slash$const_file $file_name$slash$const_file &&
  #PNRDB_disable_io=1 ./pnr_compiler ./$file_name $lef_file $v_file $map_file layers.json $file_name 1 0 | tee log && python json2gds.py $source_folder$slash$source_file $target_file && cp $target_file $gds_folder$slash$index$slash$target_file && rm -r $source_folder
  PNRDB_disable_io=1 ./pnr_compiler ./$file_name $lef_file $v_file $map_file layers.json $file_name 1 0 | tee log && python json2gds.py $source_folder$slash$source_file $target_file && cp $target_file $gds_folder$slash$index$slash$target_file && cp $source_folder$slash$Json_file $gds_folder$slash$index$slash$Json_file && rm -r $source_folder  
done


