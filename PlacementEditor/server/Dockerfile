FROM with_python

RUN \
 bash -c "source /sympy/bin/activate && pip install Flask && pip install Flask-Cors" 

RUN \
  mkdir /public

COPY server.py /public/
COPY __json /public/
