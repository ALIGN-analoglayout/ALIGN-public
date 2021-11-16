.. ALIGN documentation master file, created by
   sphinx-quickstart on Fri Jan 24 22:30:14 2020.
   You can adapt this file completely to your liking, but it should at least
   contain the root `toctree` directive.


:github_url: https://github.com/ALIGN-analoglayout/ALIGN-public

ALIGN: Analog Layout, Intelligently Generated from Netlists
===========================================================

ALIGN is an open source automatic layout generator for analog circuits jointly developed under the DARPA IDEA program by the University of Minnesota, Texas A&M University, and Intel Corporation.

The goal of ALIGN is to automatically translate an unannotated (or partially annotated) SPICE netlist of an analog circuit to a GDSII layout. The repository also releases a set of analog circuit designs.

.. toctree::
   :glob:
   :maxdepth: 1
   :caption: Get started:

   notes/flow
   notes/installation
   notes/introduction
   notes/viewer
   notes/debug
   notes/const
   notes/adding_pdk

.. toctree::
   :glob:
   :maxdepth: 1
   :caption: Datasets:

   notes/examples
   notes/database

.. toctree::
   :glob:
   :maxdepth: 1
   :caption: Notes:

   notes/contribute
   notes/success_stories


.. toctree::
   :glob:
   :maxdepth: 1
   :caption: Package Reference
   :titlesonly:
   :hidden:

   modules/align
   modules/align.schema
   modules/align.compiler
   modules/align.primitive
   modules/align.pnr
   modules/align.pdk
   modules/align.cell_fabric
   modules/align.primitive.default
   modules/align.pdk.finfet
   modules/align.utils
   modules/align.gdsconv
   modules/align.gui

.. contents:: Table of Contents
   :depth: 2
   :local:
   :backlinks: none

Indices and tables
==================

* :ref:`genindex`
* :ref:`modindex`
