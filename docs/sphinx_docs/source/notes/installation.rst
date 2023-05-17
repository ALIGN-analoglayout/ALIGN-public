Installation
=================
ALIGN is built on Python and C++ thus requires both compilers to be available on the system.

Step 0: Check prerequisites
--------------------------------
The following dependencies must be met by your system:
  * gcc >= 6.1.0 (For C++14 support)
  * python >= 3.8 (For walrus (`:=`) operator support

You may optionally install `Boost <https://www.boost.org/>`_ & `lp_solve <http://lpsolve.sourceforge.net/5.5/>`_ using your distro package manager (apt, yum etc) to save some compilation time.

.. note::
    In case you have multiple gcc versions installed on your system, we recommend explicitly setting the compiler paths as follows:

.. code-block:: bash

    export CC=/path/to/your/gcc
    export CXX=/path/to/your/g++

Step 1: Clone the ALIGN source code to your local environment
--------------------------------------------------------------------

.. code-block:: bash

    git clone https://github.com/ALIGN-analoglayout/ALIGN-public
    cd ALIGN-public


Step 2: Create a `Python virtualenv <https://docs.python.org/3/tutorial/venv.html>`_
----------------------------------------------------------------------------------------

.. note::
    You may choose to skip this step if you are doing a system-wide install for multiple users.
    Please DO NOT skip this step if you are installing for personal use and/or you are a developer.

.. code-block:: bash

    python -m venv general
    source general/bin/activate
    python -m pip install pip --upgrade


Step 3a: Install ALIGN as a USER
--------------------------------------
If you already have a working installation of Python 3.8 or above, the easiest way to install ALIGN is:

.. code-block:: bash

    pip install -v .


Step 3b: Install ALIGN as a DEVELOPER
--------------------------------------
If you are a developer, you may wish to install align with some additional flags.

For python developers:

.. code-block:: bash

    pip install -e .[test]

.. note::
    The `-e` or `--editable` flag generates links to the align package within your current directory. This allows you to modify python files and test them out immediately. You will still need to re-run this command to build your C++ collateral (when you are changing branches for example). More on that below.

For ALIGN (C++) Extension developers:

.. code-block:: bash

    pip install setuptools wheel pybind11 scikit-build cmake ninja
    pip install -v -e .[test] --no-build-isolation
    pip install -v --no-build-isolation -e . --no-deps --global-option='-DBUILD_TESTING=ON'


.. note::
    The second command doesn't just install ALIGN in-place, it also caches generated object files under an `_skbuild` subdirectory. Re-running `pip install -v -e .[test] --no-build-isolation` will reuse this cache to perform an incremental build. We add the `-v` or `--verbose` flag to be able to see build flags in the terminal.

If you want the build-type to be Release (-O3), you can issue the following three lines:

.. code-block:: bash

    pip install setuptools wheel pybind11 scikit-build cmake ninja
    pip install -v -e .[test] --no-build-isolation
    pip install -v --no-build-isolation -e . --no-deps --global-option='--build-type=Release' --global-option='-DBUILD_TESTING=ON'

or

.. code-block:: bash

    pip install setuptools wheel pybind11 scikit-build cmake ninja
    pip install -v -e .[test] --no-build-isolation
    pip install -v --no-build-isolation -e . --no-deps --global-option='--build-type=RelWithDebInfo' --global-option='-DBUILD_TESTING=ON'

Use the `Release` mode if you are mostly developing in Python and don't need the C++ debugging symbols. Use the `RelWithDebInfo` if you need both debug symbols and optimized code.

To debug runtime issues, run:

.. code-block:: bash

    python -m cProfile -o stats $ALIGN_HOME/bin/schematic2layout.py $ALIGN_HOME/examples/sc_dc_dc_converter

Then in a python shell:

.. code-block:: python

    import pstats
    from pstats import SortKey
    p = pstats.Stats('stats')
    p.sort_stats(SortKey.TIME).print_stats(20)

To run tests similar to the check-in and merge-to-master CI runs run:

.. code-block:: bash

    cd $ALIGN_HOME
    # Checkin
    pytest -vv
    CI_LEVEL='checkin' pytest -n 8 -s -vv --runnightly --maxerrors=1 -- tests/integration/
    # Merge to master
    CI_LEVEL='merge' pytest -n 8 -s -vv --runnightly --maxerrors=20 -- tests/integration/ tests/pdks



Step 4: Run ALIGN
--------------------------------------
You may run the align tool using a simple command line tool named `schematic2layout.py`
For most common cases, you will simply run the:

.. code-block:: bash

    schematic2layout.py <NETLIST_DIR> -p <PDK_DIR> -c


For instance, to build the layout for telescopic_ota:

.. code-block:: bash

    mkdir work && cd work
    schematic2layout.py ../examples/telescopic_ota -p ../pdks/FinFET14nm_Mock_PDK/


For a full list of options supported by the tool, please use the following command:

.. code-block:: bash

    schematic2layout.py -h


Step 5: View the layout
--------------------------------------
The final output GDS can be viewed using by importing in virtuoso or any GDS viewer

* `KLayout <https://github.com/KLayout/klayout>`_: GDS viewer (WSL users would need to install xming for the display to work)

* `Viewer <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/Viewer>`_: Layout viewer to view output JSON file

