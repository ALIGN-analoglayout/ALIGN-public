# Skeleton flow for translating JSON (viewer_image capatible) to GDS
````
docker build -t json_to_gds .

docker run -it json_to_gds bash -c "cd /src && ./tester"
````
