#ifndef _MST2_H_
#define _MST2_H_

#include "global.h"

namespace fastSteiner
{

void  mst2_package_init( long  n );
void  mst2_package_done();
void  mst2( long n, Point* pt, long* parent );
void  reduced_mst2( long n_terminals, long* n_points, Point* pt, Point* sorted_terms, long* parent);

int compare_points( const void*  p1, const void*  p2 );

}

#endif 

