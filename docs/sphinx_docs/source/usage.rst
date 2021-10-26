How to use ALIGN
=================

By default, the design directory is set to the examples directory. This can be modfied in the Makefile.

Native Linux environment flow
-------------------------------

.. note:: 

    Setup your own work directory
 
.. code-block:: bash 

	mkdir $ALIGN_WORK_DIR
	cd $ALIGN_WORK_DIR
	ln -s $ALIGN_HOME/build/Makefile
		
.. note:: 
    Run your first design on ALIGN

.. code-block:: bash 

	make VENV=$VENV

.. note:: 
    Run other design examples on ALIGN

.. code-block:: bash 

	make VENV=$VENV DESIGN=<design>

.. note:: 
    Explore different features of ALIGN using python arguments 

.. code-block:: bash 

	source $VENV/bin/activate
	schematic2layout.py <input_directory> -f <spice file> -s <design_name> -p <pdk path> -flat <0/1> -c (to check drc) -g (to generate image of layout)
	e.g., > schematic2layout.py $ALIGN_HOME/examples/buffer/ -f $ALIGN_HOME/examples/buffer/buffer.sp -s buffer -p $ALIGN_HOME/pdks/FinFET14nm_Mock_PDK -flat 0 -c -g

Docker based run
---------------------------

.. code-block:: bash 

	cd $ALIGN_HOME/build
	make docker DESIGN=<design>
