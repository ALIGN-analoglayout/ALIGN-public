# subckt identification

# Create a Docker image 
docker build -t topology .

# Run a Python-based test using docker

docker run --mount source=inputVol,target=/INPUT topology bash -c "source /sympy/bin/activate && cd /DEMO && source runme.sh"

# Direct run on terminal
source ./runme.sh


