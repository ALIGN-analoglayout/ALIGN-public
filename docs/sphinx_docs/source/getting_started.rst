Getting started
=================

The suggested way to run the end-to-end ALIGN flow uses a Docker container-based flow
for which the user must have docker-compose installed. The ALIGN software is installed
in a container image and Make is used to run the flow through the containers. 
The user may also use the Makefile to run the ALIGN flow through the native Linux build
of all the components in the current environment 
(assuming that all software prerequisites have been installed).

Two environment variables must be set to run the Makefile in any environment. 
The first is the ALIGN_HOME variable, which should point the top directory of the ALIGN analog system.

Clone GitHub Repository
-------------------------

.. code-block:: bash 

    git clone https://github.com/ALIGN-analoglayout/ALIGN-public

Native Linux Environment Flow
-------------------------------

You can use `install.sh <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/native_single_command_flow/install.sh>`_  to install the requirements and the native flow. Please go through `how to debug installation failures in our documentation <https://align-public.github.io/debug.html>`_ for detailed explanation and common errors during installation.

.. note:: 
    Requirements

* Python > 3.8
* gcc >= 4.2
* Ubuntu >=20.04 / RedHat >= RHEL 7

.. note:: 
    Installation

.. code-block:: bash 
    
    cd ALIGN-public
    for bash : source install.sh
    for tcsh : source install_tcsh.sh

Docker flow
------------------------------

ALIGN also supports push button flow on docker.

.. note:: 
    Requirements

* Docker-ce > 17.12
* Docker compose > 3.6

