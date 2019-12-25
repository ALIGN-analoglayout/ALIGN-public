FROM with_python

RUN \
 bash -c "source /sympy/bin/activate && pip install Flask && pip install Flask-Cors" 

COPY server.py /public
