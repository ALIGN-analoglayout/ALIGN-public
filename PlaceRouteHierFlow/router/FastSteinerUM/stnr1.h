#ifndef _STNR1_H_
#define _STNR1_H_

#include "global.h"

namespace fastSteiner
{

void  stnr1_package_init( long  max_n_points, long  flags );
void  stnr1_package_done();
double  stnr1
(
  long*   n_points,
  long    max_n_points,
  Point*  pt,
  long*   parent,
  long*   n_rounds,  
  long    max_rounds,
  long*   n_phases,
  long    max_phases_per_round,
  long    max_stnr_per_round,
  long    max_stnr_per_phase,
  double  cut_off,   
  long    flags
);

}

#endif 

