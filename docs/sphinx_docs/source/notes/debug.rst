Installation debug
====================

Error due to gcc version
--------------------------
.. code-block:: none

    ERROR:
    PlaceRouteHierFlow/pnr_compiler: /usr/lib64/libstdc++.so.6: version 'GLIBCXX_3.4.21' not found

.. note::

    C++ version is old. Please update C++ version > 4.2

    \**Inside UMN use “module load gcc/8.2.0”


Error due to xvfb library used to generate image of layout
------------------------------------------------------------
.. code-block:: none

    ERROR :
    Call to 'gds2png.sh /ALIGN-public/work/telescopic_ota/telescopic_ota_0.gds
    /ALIGN-public/work/telescopic_ota/telescopic_ota_0.png
    /ALIGN-public/align/config/image_png.rb' failed:

.. note::

   xvfb package missing

To install xvfb:

.. code-block:: bash

   sudo apt-get install xvfb

Error due to python virtual environment prerequisite missing
------------------------------------------------------------

To install python virtual environment:

.. code-block:: bash

    cd $ALIGN_HOME
    export VENV=$ALIGN_HOME/general
    python3.8 -m venv $VENV
    source $VENV/bin/activate
    pip install --upgrade pip
    pip install -e .
    deactivate


Error due to klayout prerequisite missing
------------------------------------------------------------
.. code-block:: none

    ERROR:
    Call to klayout failed.

.. note::

    Install klayout tool for visualization

To install klayout:

.. code-block:: bash

    curl -o /klayout_0.25.4-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-18/klayout_0.25.4-1_amd64.deb
    apt-get install -yq /klayout_0.25.4-1_amd64.deb

Reinstalling ALIGN
------------------------------------------------------------
To update pip and install align again:

.. note::
    remove _skbuild directory

Error due to g++ package not updated
------------------------------------------------------------
.. code-block:: none

    ERROR:
    <builtin>: recipe for target 'capplacer.o' failed
    make[1]: *** [capplacer.o] Error 1
    make[1]: Leaving directory '$ALIGN_HOME/PlaceRouteHierFlow/cap_placer'
    Makefile:42: recipe for target 'subsystem' failed
    make: *** [subsystem] Error 2

.. note::

    Check for errors during “sudo apt-get update”. It can be due to the older Ubuntu version and might need Ubuntu update.

Warnings that can be ignored:
-------------------------------

* WriteJSON.cpp:144:1: warning: defined but not used [-Wunused-function]
* GcellDetailRouter.cpp:2550:7: warning: unused variable ‘LLx’ [-Wunused-variable]
* MNASimulation.cpp:: warning: comparison between signed and unsigned integer expressions [-Wsign-compare]
* GcellDetailRouter.cpp:2571:16: warning: comparison between signed and unsigned integer expressions [-Wsign-compare]

.. note::
    Ignore these warnings
