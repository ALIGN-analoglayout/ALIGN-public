`darpaalign/align-public` has the latest version of [ALIGN-public](https://github.com/ALIGN-analoglayout/ALIGN-public) installed on a Ubuntu 22.04 image.
# Usage
## Pull image
To pull this image use:
```
docker pull darpaalign/align-public:latest 
```
To create your own image with modifications, use the `dockerfile` in this directory.

## Source code
The source code of the ALIGN version installed is in the directory `/home/align/ALIGN-public` in the docker image. The examples and mock PDK that are packaged with ALIGN are available in this directory.

# Building a personalized image
Create a dockerfile with the following contents:
```
FROM darpaalign/align-public AS env
ARG UID=0
ARG GID=0
RUN if [ "$GID" -ne "0" ] ; then echo $GID && groupadd -g $GID -o align; else  echo 1000 && groupadd -g 1000 -o align; fi
RUN if [ "$UID" -ne "0" ] ; then useradd -m -u $UID -g $GID -p align -o -s /bin/bash align; else useradd -m -u 1000 -g 1000 -p align -o -s /bin/bash align; fi
RUN chown -R align /work
USER align
WORKDIR /work
```
Run the command  `docker build --build-arg UID=$(id -u) --build-arg GID=$(id -g) -t <your_preferred_name> .` to create a corresponding docker image that generates files with appropriate file permissions in Linux.

## Mount host directories inside the image
Use the following command to mount a custom PDK/schematic directory in the host machine inside the docker image:
```
docker run -i -t --mount src=<absolute_path>/<PDK_DIR>,target=/<PDK_DIR>,type=bind \
                 --mount src=<absolute_path>/<SCH_DIR>,target=/<SCH_DIR>,type=bind  \
                 --mount src=<RUN_DIR>,target=/work,type=bind \
                 -w /work <your_preferred_name> bash
```
The paths in the host machine appear as mounted volumes inside the docker container.

## Run
To run ALIGN, use `schematic2layout.py -p /<PDK_DIR> /<SCH_DIR>` in the bash shell inside the docker container.
Refer to [ALIGN-public](https://github.com/ALIGN-analoglayout/ALIGN-public) for detailed documentation on the usage of `schematic2layout.py`.

## Batch mode
`run_align` is a script inside docker that runs ALIGN on a schematic/PDK directory specified using the env variables `ALIGN_CKT_DIR`/`ALIGN_PDK_DIR` respectively.
Usage:
```
docker run -e ALIGN_PDK_DIR=/<PDK_DIR> -e ALIGN_CKT_DIR=/<SCH_DIR> \
                 --mount src=<absolute_path>/<PDK_DIR>,target=/<PDK_DIR>,type=bind \
                 --mount src=<absolute_path>/<SCH_DIR>,target=/<SCH_DIR>,type=bind  \
                 --mount src=<RUN_DIR>,target=/work,type=bind \
                 -w /work <your_preferred_name> run_align
```
This command will automatically generate the ALIGN outputs in the `<RUN_DIR>`.
