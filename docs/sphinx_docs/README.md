ALIGN documentation folder
================================

Requirements
------------
* sphinx
* sphinx-gallery
* sphinx_rtd_theme

Build documents
---------------
build:
```
make html
```

The generated files will be available at `../../../align_documentation`. If there is an existing folder please remove and rerun.

check locally
--------------
```
cd ../../../align_documentation/html
firefox index.html
```

Publishing your html files
------------------------------

Align documentation is hosted from 'gh-pages' branch of ALIGN. You can push yout html files there to update the documenation.
