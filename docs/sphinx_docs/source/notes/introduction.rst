Introduction by Example
========================

Run your first design from the example directory:

.. code-block:: bash

	source $VENV/bin/activate
	schematic2layout.py <input_directory> -p <pdk path>
	e.g., > schematic2layout.py $ALIGN_HOME/examples/buffer/ -p $ALIGN_HOME/pdks/FinFET14nm_Mock_PDK

.. note::
	ALIGN assumes folder name, file name, and top design name to be identical unless provided specifically. You can also specify them using command line arguments.

.. code-block:: bash

	source $VENV/bin/activate
	schematic2layout.py <input_directory> -f <spice file> -s <design_name> -p <pdk path> -flat <0/1> -c (to check drc) -g (to generate image of layout)
	e.g., > schematic2layout.py $ALIGN_HOME/examples/buffer/ -f $ALIGN_HOME/examples/buffer/buffer.sp -s buffer -p $ALIGN_HOME/pdks/FinFET14nm_Mock_PDK -flat 0 -c -g

For a full list of options supported by the tool, please use the following command:

.. code-block:: bash

    schematic2layout.py -h

