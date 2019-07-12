#ifndef _TRIPLES_H_
#define _TRIPLES_H_

#include "global.h"

namespace fastSteiner
{

void  gain_package_init( long n );
void  gain_package_done();

void  preprocess_edges
(
  long   n_edges,
  Edge*  edge,
  Edge*  edge2,
  long   unsorted
);

void  remove_negative_gain_triples
(
  long*    n_triples,
  Triple*  triple,
  Edge*    edge
);

void  triple_package_init( long n );
void  triple_package_done();

void  collect_triples
(
  long      n_pts,
  Point*    pt,
  long*     n_triples,
  long      max_n_triples,
  Triple*   triple,
  Edge*     edge
);

}

#endif
