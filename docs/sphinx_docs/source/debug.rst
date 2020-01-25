How to debug installation failures
===============================================

Despite using install.sh if something fails, we have collected a basic set of errors and how to resolve them.


Error due to gcc version
--------------------------
.. code-block:: none 

    ERROR:
    PlaceRouteHierFlow/pnr_compiler: /usr/lib64/libstdc++.so.6: version 'GLIBCXX_3.4.21' not found

.. note:: 
    
    C++ version is old. Please update C++ version > 4.2
    Inside UMN use “module load gcc/8.2.0” 

Error due to LD_LIBRARY_PATH prerequisite missing 
--------------------------------------------------
.. code-block:: none 

    ERROR:
    Unable to load lpsolve shared library (liblpsolve55.so).
    It is probably not in the correct path.
    LP test flag 2
    TotNumberOfNest 14 TotNumberOfSTs 70
    align.cmdline ERROR : Fatal Error. Cannot proceed

.. note:: 

    It can be due to LD_LIBRARY_PATH not present or LD_LIBRARY_PATH path not correct
    
To install lpsolve: 

.. code-block:: bash 

    git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git


To set lpsolve environment path:

.. code-block:: bash 

    Ubuntu/bash: export LD_LIBRARY_PATH=$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
    RedHat/tcsh: Setenv LD_LIBRARY_PATH $ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
 
Error due to xvfb library used to generate image of layout 
------------------------------------------------------------
.. code-block:: none 

    ERROR :
    Call to 'gds2png.sh /ALIGN-public/work/telescopic_ota/telescopic_ota_0.gds /ALIGN-public/work/telescopic_ota/telescopic_ota_0.png /ALIGN-public/align/config/image_png.rb' failed:

.. note:: 
    
   xvfb package missing

To install xvfb: 

.. code-block:: bash 

   sudo apt-get install xvfb

Error due to lpsolve library prerequisite missing 
------------------------------------------------------------
.. code-block:: none 

    ERROR:
    ./router/GcellGlobalRouter.h:47:10: fatal error: lp_lib.h: No such file or directory
    #include "lp_lib.h"
          ^~~~~~~~~~
    compilation terminated.

.. note:: 
    
    It can be due to LD_LIBRARY_PATH not configured correctly

To install lpsolve: 

.. code-block:: bash 

    git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git

To set lpsolve environment path:

.. code-block:: bash 

    Ubuntu/bash: export LP_DIR=$ALIGN_HOME/lpsolve
    RedHat/tcsh: setenv LD_DIR $ALIGN_HOME/lpsolve

Error due to googletest prerequisite missing 
------------------------------------------------------------
.. code-block:: none 

    ERROR:
    unit_tests.cpp:2:10: fatal error: gtest/gtest.h: No such file or directory
     #include <gtest/gtest.h>
          ^~~~~~~~~~~~~~~
    compilation terminated.

.. note:: 
    
    It can be due to googletest not present or googletest path not correct

To install googletest:

.. code-block:: bash 

    cd $ALIGN_HOME
    git clone https://github.com/google/googletest
    cd googletest/
    cmake CMakeLists.txt
    make
    mkdir googletest/mybuild
    cp -r lib googletest/mybuild/.

To set googletest path:

.. code-block:: bash 

    Ubuntu/bash: export GTEST_DIR=$ALIGN_HOME/googletest/googletest/
    RedHat/tcsh: setenv GTEST_DIR $ALIGN_HOME/googletest/googletest/

Error due to JSON prerequisite missing 
------------------------------------------------------------
.. code-block:: none 

    ERROR:
    PnRdatabase.h:23:10: fatal error: nlohmann/json.hpp: No such file or directory
     #include <nlohmann/json.hpp>
          ^~~~~~~~~~~~~~~~~~~
    compilation terminated.

.. note:: 
    
    It can be due to JSON not present or JSON path not correct

To install JSON:

.. code-block:: bash 
    
    cd $ALIGN_HOME
    git clone https://github.com/nlohmann/json.git

To set JSON path:

.. code-block:: bash 

    Ubuntu/bash: export JSON=$ALIGN_HOME/json
    RedHat/tcsh: setenv JSON $ALIGN_HOME/json

Error due to python virtual environment prerequisite missing
------------------------------------------------------------
.. code-block:: none 

    ERROR:
    /bin/bash: /opt/venv/bin/activate: No such file or directory

.. note:: 
    
    ALIGN is installed inside a python virtual environment. The default path of the virtual environment is assumed to be /opt/venv/bin/activate. You can edit the makefile to the path of your virtual environment or pass the virtual environment path as a parameter.

To install python virtual environment:

.. code-block:: bash 
    
    cd $ALIGN_HOME
    export VENV=$ALIGN_HOME/general
    python3.6 -m venv $VENV
    source $VENV/bin/activate
    pip install --upgrade pip
    pip install -e .
    deactivate

    
To set virtual environment path:

.. code-block:: bash 
    
    make  VENV=$VENV DESIGN=telescopic_ota 

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

Error due to missing align installation
------------------------------------------------------------
.. code-block:: none 

    ERROR:
    python: can't open file
    '$ALIGN_HOME/general/bin/schematic2layout.py':
    [Errno 2] No such file or directory
    Makefile:36: recipe for target 'telescopic_ota/telescopic_ota_0.png' failed
    make: *** [telescopic_ota/telescopic_ota_0.png] Error 2

.. note:: 
    
    This happens due to issues with pip version resulting in missing align package installation.

To update pip and install align:

.. code-block:: bash 
    
    cd $ALIGN_HOME
    source $VENV/bin/activate
    pip Install --upgrade pip 
    pip Install -e . 
    deactivate

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

