Contribute to ALIGN
===========================================================

ALIGN is an open-source tool for analog layout generation. We appreciate any contribution to ALIGN.
Layout generation requires multiple components for the flow to produce a good layout. There are multiple ways you can contribute.

Some example contributions
---------------------------
* New analog designs can be added to ALIGN `database <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/CircuitsDatabase>`_
* New open source `PDKs <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/pdks/>`_
* New primitives in `cell generator <https://github.com/ALIGN-analoglayout/ALIGN-public/blob/master/align/primitive/main.py>`_
* Adding `unit-tests <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/tests>`_
* `Documentation <https://github.com/ALIGN-analoglayout/ALIGN-public/tree/master/docs>`_
* `Bug-fixes <https://github.com/ALIGN-analoglayout/ALIGN-public/issues>`_
* Feature recommendations



Install ALIGN setup as a developer
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

.. note::
    The second command doesn't just install ALIGN in-place, it also caches generated object files etc. under an `_skbuild` subdirectory. Re-running `pip install -v -e .[test] --no-build-isolation` will reuse this cache to perform an incremental build. We add the `-v` or `--verbose` flag to be able to see build flags in the terminal.

If you want the build-type to be Release (-O3), you can issue the following three lines:

.. code-block:: bash

    pip install setuptools wheel pybind11 scikit-build cmake ninja
    pip install -v -e .[test] --no-build-isolation
    pip install -v --no-build-isolation -e . --no-deps --install-option='--build-type=Release'

or

.. code-block:: bash

    pip install setuptools wheel pybind11 scikit-build cmake ninja
    pip install -v -e .[test] --no-build-isolation
    pip install -v --no-build-isolation -e . --no-deps --install-option='--build-type=RelWithDebInfo'

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
