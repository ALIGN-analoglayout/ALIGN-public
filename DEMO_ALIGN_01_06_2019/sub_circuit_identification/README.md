
# Installation of required packages
docker build -t topology .

# Run a python-based test using docker

docker run -it --mount source=inputVol,target=/INPUT topology bash -c "cd /DEMO && source runme.sh"

# Copy data from docker to local machine
source ./runme.sh


