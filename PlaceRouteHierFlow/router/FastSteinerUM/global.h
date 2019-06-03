#ifndef  _GLOBAL_H_
#define  _GLOBAL_H_

#include <stdio.h>

namespace fastSteiner
{

#define  UNDEFINED   -1
#define  FALSE        0
#define  TRUE         1
#define  SQRT_TWO     1.4142135623730950488016887242097
#define  INFTY        1e20

/* bit flags */

#define  PRINT_RESULTS   1
#define  PRINT_TREE      2
#define  PRINT_ROUNDS    4
#define  PRINT_PHASES    8
#define  ALL_FLAGS (PRINT_RESULTS + PRINT_TREE + PRINT_ROUNDS + PRINT_PHASES)

/* default parameters */

#define DEFAULT_METRIC            RECTILINEAR
#define DEFAULT_FLAGS             PRINT_RESULTS
#define DEFAULT_MAX_ROUNDS        999999
#define DEFAULT_PHASES_PER_ROUND  999999
#define DEFAULT_STNR_PER_ROUND    999999
#define DEFAULT_STNR_PER_PHASE    999999
#define DEFAULT_TIMED_STNR_RUNS   1
#define DEFAULT_TIMED_MST_RUNS    1
#define DEFAULT_SEED              1
#define DEFAULT_CUT_OFF           0


typedef  enum metric_enum {RECTILINEAR, OCTILINEAR} Metric;

typedef  struct point 
         {
           double  x, y;
         } Point;

typedef  long nn_array[8];

typedef  struct triple_struct 
         { 
           long  id;
           long  pt[3];
           double  stnr_x, stnr_y;
           double  length;
           double  gain;
           long  e[2];
           char  repl[2][2];
         } Triple;

typedef  struct edge_struct
         {
           long    id;
           long    pt1, pt2;
           double  len;
           long    free;
         } Edge;

}

#endif  /* _GLOBAL_H_ */
