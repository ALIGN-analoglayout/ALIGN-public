#!/bin/bash

echo "Setting-up Docker Environment"

###1
cd ./Viewer/
docker build -t viewer_image .
clear
cd ..

###2

cd ./CellFabric/
docker build -f Dockerfile.build.python -t with_python .
docker build -t fabric .
clear
cd ..

###3

cd ./sub_circuit_identification/

docker build -t topology1 .
clear
cd ..

###4

cd ./sub_circuit_identification_OTA/

docker build -t topology .
clear

###5

docker run -it --mount source=inputVol,target=/INPUT topology bash -c "cd /DEMO && source runme.sh"

gvim ./results/OTA.v
#read inputvar1
clear

###6

echo "Primitive Cell Generation: 1X4 Aspect Ratio"
echo "Inputs: nfin = 5, ngate = 2, X_cells = 4, Y_cells = 1>"
read inputvar1
cd ..

cd ./CellFabric/

#####1

#docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric_Asap7.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"

#docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"

#xdg-open http://localhost:8085
#clear
#echo "Primitive Cell: Cell Generation"
#read inputvar1

#####2

#docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric_Asap7_1.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"

#docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"

#xdg-open http://localhost:8085
#clear
#echo "Primitive Cell: Cell Generation"
#read inputvar1

######3

docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric_Asap7_2.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"

docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"

xdg-open http://localhost:8085
clear
echo "Primitive Cell Generation: 2X2 Aspect Ratio"
echo "Inputs: nfin = 5, ngate = 2, X_cells = 2, Y_cells = 2>"
read inputvar1

####4
docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric_Asap7_3.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"

docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"

xdg-open http://localhost:8085
clear
echo "Primitive Cell Generation: DP Cell Generation"
echo "Inputs: nfin = 10, ngate = 2, X_cells = 4, Y_cells = 2>"
read inputvar1

####5

docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric_dp_Asap7.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"

docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"

xdg-open http://localhost:8085
clear

###6a
echo "OTA Place and Route>"
read inputvar1
cd ..
cd ./GDS_viewer/

xhost local:root
docker build -t darpaalign/klayout .
clear
docker run --env="DISPLAY" --env="QT_X11_NO_MITSHM=1" --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" --mount source=inputVol,target=/INPUT darpaalign/klayout bash -c "cd /DEMO && klayout -gr test.txt OTA.gds"
clear
cd ..

###7

echo "Example2: Switched Capacitor Filter"
read inputvar1
cd ./sub_circuit_identification/
docker run -it --mount source=inputVol,target=/INPUT topology1 bash -c "cd /DEMO1 && source runme.sh"
gvim ./results/switched_cap_filter.v
#read inputvar1
clear
###8

echo "Capacitor: UnitCell Generation"
echo "Inputs: Unit_Cap = 10fF, X_cells = 1, Y_cells = 1>"
read inputvar1
cd ..
cd ./CellFabric/

docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric_cap.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"

docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"

xdg-open http://localhost:8085
clear

echo "Capacitor: Array Generation"
echo "Inputs: Unit_Cap = 10fF, X_cells = 3, Y_cells = 2>"
read inputvar1
docker run --mount source=inputVol,target=/INPUT fabric bash -c "source /sympy/bin/activate && cd /scripts && python fabric_cap_array.py && python removeDuplicates.py && cp mydesign_dr_globalrouting.json /INPUT"

docker run --mount source=inputVol,target=/public/INPUT --rm -d -p 8085:8000 viewer_image bash -c "source /sympy/bin/activate && cd /public && python -m http.server"

xdg-open http://localhost:8085
cd ..
clear

echo "Switched Capacitor Filter Place and Route>"
read inputvar1
cd ..
cd ./GDS_viewer/

xhost local:root
docker build -t darpaalign/klayout .
clear
docker run --env="DISPLAY" --env="QT_X11_NO_MITSHM=1" --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" --mount source=inputVol,target=/INPUT darpaalign/klayout bash -c "cd /DEMO && klayout -gr test1.txt switched_cap_filter.gds"
clear
cd ..
#echo "################################### THANK YOU from ALIGN TEAM ###################################"


