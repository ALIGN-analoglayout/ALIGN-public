# Installation of image 

docker build -t placeroute_image .

# Run a test using docker

./run_in_docker.sh

# Attention of third-party ILP solver
In our placer, a third-party ILP solver lp_solve is required. The current supported version is lp_solve 5.5.2.5.
Please download the codes from http://lpsolve.sourceforge.net/5.5/.

To compile locally:

   LP_DIR=<path_to_lp> make
