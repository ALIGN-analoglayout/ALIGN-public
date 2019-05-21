FROM tally as cell_fabric_image

RUN \
    mkdir -p /scripts

ADD . /Cell_Fabric_Common/

RUN \
    bash -c "source general/bin/activate && cd /Cell_Fabric_Common/ && pip install ."











