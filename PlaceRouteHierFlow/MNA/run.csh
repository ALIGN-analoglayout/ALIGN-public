#！/bin/bash

file_name=five_transistor_ota
file_path=/home/yaguang/Desktop/opt/ALIGN-body-contact/ALIGN-public/examples/
sp_file=.sp
json_file=.json
png_file=.png
slash=/
pnr=_0
pnr_file=$file_name$pnr
bk=_bk
blank=_

design=$file_name$sp_file
design_dir=$file_path$file_name
work_dir=/home/yaguang/Desktop/src/work_body_contact
result_dir=/pnr_output/Results/

cp generate.py $design_dir

objective_file=$file_name$result_dir$file_name$json_file
objective_png_file=$file_name$result_dir$pnr_file$png_file

db=db_file
mkdir $db
cd $db && mkdir $file_name && cd ..

export LD_LIBRARY_PATH=/usr/local/lib/lpsolve/lp_solve_5.5.2.5_dev_ux64/
export ALIGN_HOME=/home/yaguang/Desktop/opt/ALIGN-body-contact/ALIGN-public
source general/bin/activate

for i in $(seq 0 1 100)
do
  dest_file=$db$slash$file_name$slash$file_name$blank$i$json_file
  dest_png_file=$db$slash$file_name$slash$file_name$blank$i$png_file
  cd $design_dir
  python generate.py $design && mv $design$bk $design && cd $work_dir &&make DESIGN=$file_name && echo $png_file && echo $dest_png_file && cp $objective_file $dest_file && cp $objective_png_file $dest_png_file  && rm -r $file_name
done
