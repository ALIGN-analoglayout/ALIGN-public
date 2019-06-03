#include  <assert.h>
#include  <string.h>
#include  <stdlib.h>
#include  "global.h"
#include  "random.h"
#include  "dist.h"
#include  "err.h"

namespace fastSteiner
{

long  octant
(
  Point  from,
  Point  to
);

/***************************************************************************/
/***************************************************************************/
/*
  For efficiency purposes auxiliary arrays are allocated as globals 
*/

long    max_arrays_size = 0;
nn_array*  nn   = (nn_array*)NULL;
Point*  sheared = (Point*)NULL;
long*  sorted   = (long*)NULL;
long*  aux      = (long*)NULL;  

/***************************************************************************/
/***************************************************************************/
/*
  resize the auxiliary arrays to fit the specified number of points 
*/

void  allocate_nn_arrays( long  n )
{
  if( max_arrays_size < n ) 
  {
    //nn      = (nn_array*)realloc( (void*)nn, (size_t)n*sizeof(nn_array) );
    //sheared = (Point*)realloc( (void*)sheared, (size_t)n*sizeof(Point) );
    //sorted  = (long*)realloc( (void*)sorted, (size_t)n*sizeof(long) );
    //aux     = (long*)realloc( (void*)aux, (size_t)n*sizeof(long) );

    nn_array* tmp_nn= static_cast<nn_array *>( realloc( (void*)nn, (size_t)n*sizeof(nn_array) ) );
    if(tmp_nn == NULL) {
      free(nn);
      err_exit( "Cannot allocate memory nn in allocate_nn_arrays!" );
    } else {
      nn = tmp_nn;
    }

    Point* tmp_sheared= static_cast<Point *>( realloc( (void*)sheared, (size_t)n*sizeof(Point) ) );
    if(tmp_sheared == NULL) {
      free(sheared);
      err_exit( "Cannot allocate memory sheared in allocate_nn_arrays!" );
    } else {
      sheared = tmp_sheared;
    }

    long* tmp_sorted= static_cast<long *>( realloc( (void*)sorted, (size_t)n*sizeof(long) ) );
    if(tmp_sorted == NULL) {
      free(sorted);
      err_exit( "Cannot allocate memory sorted in allocate_nn_arrays!" );
    } else {
      sorted = tmp_sorted;
    }

    long* tmp_aux= static_cast<long *>( realloc( (void*)aux, (size_t)n*sizeof(long) ) );
    if(tmp_aux == NULL) {
      free(aux);
      err_exit( "Cannot allocate memory aux in allocate_nn_arrays!" );
    } else {
      aux = tmp_aux;
    }

    if( !nn || !sheared || !sorted || !aux )
    {
      err_exit( "Cannot allocate memory in allocate_nn_arrays!" );
    }
    max_arrays_size = n;
  }
}

/***************************************************************************/
/***************************************************************************/
/*
  free memory used by auxiliary arrays
*/

void  deallocate_nn_arrays()
{
  max_arrays_size = 0;
  if( nn )
  {
    free( (void*)nn );
    nn = (nn_array*)NULL;
  }
  if( sheared )
  {
    free( (void*)sheared );
    sheared = (Point*)NULL;
  }
  if( sorted )
  {
    free( (void*)sorted );
    sorted = (long*)NULL;
  }
  if( aux )
  {
    free( (void*)aux );
    aux = (long*)NULL;
  }

}

/***************************************************************************/
/***************************************************************************/
/*
  comparison function for use in quicksort
*/

static  int compare_x
( 
  const void*  i, 
  const void*  j 
)
{
  Point*  pi = sheared + *((long*)i);
  Point*  pj = sheared + *((long*)j);

  if( pi->x > pj->x ) return  +1;
  if( pi->x < pj->x ) return  -1;
  if( pi->y > pj->y ) return  +1;
  if( pi->y < pj->y ) return  -1;

#ifdef DEBUG2
    printf( "Duplicate points!\n" );
#endif

  return  0;
}

/***************************************************************************/
/***************************************************************************/
/*
  Combine step of the Guibas-Stolfi divide-and-conquer NE nearest neighbor
  algorithm. For efficiency purposes SW nearest neighbors are computed 
  at the same time.
*/

inline void  ne_sw_combine
(
  long    left,
  long    mid,
  long    right,
  Point*  pt,
  long*   sorted,
  long*   aux,
  long    oct,
  nn_array*  nn
)
{
  long    i, j, k; 
  long    i1;
  long    i2; 
  long    best_i2;     /* index of current best nearest-neighbor */
  double  best_dist;   /* distance to best nearest-neighbor      */
  double  d, y2;

#ifdef DEBUG
  assert( right > mid );
  assert( mid > left );
#endif

  /*
    update north-east nearest neighbors accross the mid-line
  */

  i1 = left;
  i2 = mid;   y2 = pt[ sorted[i2] ].y;

  while( (i1 < mid) && (pt[ sorted[i1] ].y >= y2) )
  {
    i1++;
  }
  
  if( i1 < mid )
  {
    best_i2   = i2;
    best_dist = l1_dist( pt + sorted[i1], pt + sorted[best_i2] );
    i2++;

    while( (i1 < mid) && (i2 < right) )
    {
      if( pt[ sorted[i1] ].y < pt[ sorted[i2] ].y )
      {
        d = l1_dist( pt + sorted[i1], pt + sorted[i2] );
        if( d < best_dist ) 
        {
          best_i2   = i2;
          best_dist = d;
        }
        i2++;
      }
      else 
      {
        if( (nn[ sorted[i1] ][oct] == -1) || 
            ( best_dist < l1_dist( pt + sorted[i1], pt + nn[ sorted[i1] ][oct] ) ) 
           )
        {
          nn[ sorted[i1] ][oct] = sorted[best_i2];
        }
        i1++;
        if( i1 < mid )
        {
          best_dist = l1_dist( pt + sorted[i1], pt + sorted[best_i2] );
        }
      }    
    }

    while( i1 < mid )
    {
      if( (nn[ sorted[i1] ][oct] == -1) || 
          ( l1_dist( pt + sorted[i1], pt + sorted[best_i2] ) < 
            l1_dist( pt + sorted[i1], pt + nn[ sorted[i1] ][oct]) ) 
        )
      {
        nn[ sorted[i1] ][oct] = sorted[best_i2];
      }
      i1++;
    }
  }
  /*
    repeat for south-west nearest neighbors
  */

  oct = (oct + 4) % 8;

  i1 = right - 1;
  i2 = mid - 1;   y2 = pt[ sorted[i2] ].y;
     
  while( (i1 >= mid) && (pt[ sorted[i1] ].y <= y2) )
  {
    i1--;
  }

  if( i1 >= mid )
  {
    best_i2   = i2;
    best_dist = l1_dist( pt + sorted[i1], pt + sorted[best_i2] );
    i2--;

    while( (i1 >= mid) && (i2 >= left) )
    {
      if( pt[ sorted[i1] ].y > pt[ sorted[i2] ].y )
      {
        d = l1_dist( pt + sorted[i1], pt + sorted[i2] );
        if( d < best_dist ) 
        {
          best_i2   = i2;   
          best_dist = d;
        }
        i2--;
      }
      else 
      {
        if( (nn[ sorted[i1] ][oct] == -1) || 
            ( best_dist < l1_dist( pt + sorted[i1], pt + nn[ sorted[i1] ][oct]) ) 
           )
        {
          nn[ sorted[i1] ][oct] = sorted[best_i2];
        }
        i1--;
        if( i1 >= mid )
        {
          best_dist = l1_dist( pt + sorted[i1], pt + sorted[best_i2] );
        }
      }    
    }

    while( i1 >= mid )
    {
      if( (nn[ sorted[i1] ][oct] == -1) || 
          ( l1_dist( pt + sorted[i1], pt + sorted[best_i2] ) < 
            l1_dist( pt + sorted[i1], pt + nn[ sorted[i1] ][oct]) ) 
        )
      {
        nn[ sorted[i1] ][oct] = sorted[best_i2];
      }
      i1--;
    }
  }

  /*
    merge sorted[left..mid-1] with sorted[mid..right-1] by y-coordinate
  */

  i = left;  /* first unprocessed element in left  list  */
  j = mid;   /* first unprocessed element in right list  */
  k = left;  /* first free available slot in output list */

  while( (i < mid) && (j < right) )
  {
    if( pt[ sorted[i] ].y >= pt[ sorted[j] ].y )
    {
      aux[k++] = sorted[i++]; 
    }
    else 
    {
      aux[k++] = sorted[j++]; 
    }
  }

  /*
    copy leftovers 
  */
  while( i < mid   ) {  aux[k++] = sorted[i++]; }
  while( j < right ) {  aux[k++] = sorted[j++]; }

  /*
    now copy sorted points from 'aux' to 'sorted' 
  */

  memcpy( (void*)(sorted+left),             /* destination */
          (void*)(aux+left),             /* source      */
          (size_t)(right-left)*sizeof(long) /* number of bytes */ 
        );

}

/***************************************************************************/
/***************************************************************************/
/*
   Guibas-Stolfi divide-and conquer algorithm for computing all
   north-east and south-west nearest neighbors for points indexed
   by {sorted[left],...,sorted[right-1]} 
*/

void  ne_sw_nearest_neighbors
(
  long    left,
  long    right,
  Point*  pt,
  long*   sorted,
  long*   aux,
  long    oct,
  nn_array*  nn
)
{
  //long   mid;

#ifdef DEBUG
  assert( right > left );
#endif

  if( right == left + 1 )  
  {
    nn[ sorted[left] ][oct] = nn[ sorted[left]][(oct+4) % 8] = -1;
  }
  else
  {
    long mid = (left + right) / 2;
    ne_sw_nearest_neighbors( left, mid, pt, sorted, aux, oct, nn );
    ne_sw_nearest_neighbors( mid, right, pt, sorted, aux, oct, nn );
    ne_sw_combine( left, mid, right, pt, sorted, aux, oct, nn );
  }
}

/***************************************************************************/
/***************************************************************************/
/*
  For each terminal, compute RECTILINEAR nearest neighbors in the 8 octants
*/

void  dq_nearest_neighbors
(
  long      n,
  Point*    pt,
  nn_array*  nn
)
{
  long   i, j, tmp, oct;

  double   shear[4][4];
 
  

  if( metric == RECTILINEAR )
  {
  double   rectilinear_shear[4][4] = {
                         {1, -1,  0,  2},
                         {2,  0, -1,  1},
                         {1,  1, -2,  0},
                         {0,  2, -1, -1}
                       };
//    shear = rectilinear_shear;
    memcpy(shear,rectilinear_shear,sizeof(shear));
  }
  else
  {
  double  octilinear_shear[4][4] = {
                         {1, -1,  0,  SQRT_TWO},
                         {SQRT_TWO,  0, -1,  1},
                         {1,  1, -SQRT_TWO,  0},
                         {0,  SQRT_TWO, -1, -1}
                       };
//    shear = octilinear_shear;
    memcpy(shear,octilinear_shear,sizeof(shear));
  }

  for( oct = 0;  oct < 4;  oct++ )
  {
    for( i = 0;   i < n;   i++ )
    {
      sheared[i].x = shear[oct][0]*pt[i].x + shear[oct][1]*pt[i].y;
      sheared[i].y = shear[oct][2]*pt[i].x + shear[oct][3]*pt[i].y;
      sorted[i] = i;
    }

    for( i = 0;  i < n/2;  i++ )
    {
      j = unif_rand( n );
      tmp = sorted[i];  sorted[i] = sorted[j];  sorted[j] = tmp;
    }
    qsort( sorted, n, sizeof(long), compare_x );

#ifdef DEBUG
    assert( is_sorted( sorted, n, sizeof(long), compare_x ) );
#endif

    ne_sw_nearest_neighbors( 0, n, sheared, sorted, aux, oct, nn );
  }

}

}

/***************************************************************************/
/***************************************************************************/
