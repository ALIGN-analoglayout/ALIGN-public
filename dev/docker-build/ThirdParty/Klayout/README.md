# GDS Viewer

You can use Klayout to view GDS files.
To build it, use:
````
docker build -t darpaalign/klayout .
````
or grab it from hub.docker.com using:
````
docker pull darpaalign/klayout
````
Use `./flow.sh` to run the router and view the results.
You need to be on a Linux box for this. Try `xhost +` if you are having trouble.


You can use Klayout to convert GDS files to PNG.


To do this, use the klayout image but append the following command:

<run klayout image> ./gds2png.sh <infile> <outfile>


