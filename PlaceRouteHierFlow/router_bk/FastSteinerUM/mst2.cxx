#include  <stdlib.h>
#include  <stdio.h>
#include   <assert.h>
#include  "global.h"
#include  "neighbors.h"
#include  "random.h"
#include  "dist.h"
#include  "heap.h"
#include  "err.h"

namespace fastSteiner
{

long   max_n_points = 0;
long*  degree;

void  mst2_package_init( long  n )
{
  allocate_heap( n );
  allocate_nn_arrays( n );

  if( max_n_points < n )
  {
    //degree = (long*)realloc( (void*)degree, (size_t)n*sizeof(Edge) );
    long* tmp_degree= static_cast<long *>( realloc( (void*)degree, (size_t)n*sizeof(Edge) ) );
    if(tmp_degree == NULL) {
      free(degree);
      err_exit( "Cannot allocate memory in mst2_package_init()!" );
    } else {
      degree = tmp_degree;
    }
    max_n_points = n;
  }
    
  if( !degree )
  {
    err_exit( "Cannot allocate memory in mst2_package_init()!" );
  }
}

/****************************************************************************/
/*
*/

void  mst2_package_done()
{
  deallocate_heap();
  deallocate_nn_arrays();
  if( degree  ) { free( (void*)degree);   degree  = (long*)NULL; }
  max_n_points = 0;  
}  

/***************************************************************************/
/***************************************************************************/
/*
  comparison function for use in quicksort
*/

int compare_points
(
  const void*  p1,
  const void*  p2
)
{
  if( ((Point*)p1)->x < ((Point*)p2)->x ) return -1;
  if( ((Point*)p1)->x > ((Point*)p2)->x ) return +1;
  if( ((Point*)p1)->y < ((Point*)p2)->y ) return -1;
  if( ((Point*)p1)->y > ((Point*)p2)->y ) return +1;

  return 0;
}


/****************************************************************************/
/*
*/

void  mst2
( 
  long    n,
  Point*  pt, 
  long*   parent
)
{
  long    k, nn1;
  double  d;
  long    oct;
  long    root = 0;
  extern  nn_array*  nn;

  mst2_package_init( n );        /* reallocate array, if needed */

  dq_nearest_neighbors( n, pt, nn );

  /* 
     Binary heap implementation of Prim's algorithm.
     Runs in O(n*log(n)) time since at most 8n edges are considered
  */

  heap_init( n );
  heap_insert( root, 0 );
  parent[root] = root;

  for( k = 0;  k < n;  k++ )   /* n points to be extracted from heap */
  {
    long i = heap_delete_min();

//#ifdef DEBUG
    assert( (i >= 0) && (i < n) );
//#endif 

    /*
      pt[i] entered the tree, update heap keys for its neighbors
    */
    for( oct = 0;  oct < 8;  oct++ )
    {
      nn1 = nn[i][oct]; 
      if( nn1 >= 0 )
      {
        d  = dist( pt[i], pt[nn1] );
        if( in_heap(nn1) && (d < heap_key(nn1)) )
        {
          heap_decrease_key( nn1, d );
          parent[nn1] = i;
        } 
        else if( never_seen(nn1) )
        {
          heap_insert( nn1, d );
          parent[nn1] = i;
        }
      }
    }
  }
}

/****************************************************************************/
/*
*/

void  reduced_mst2
( 
  long    n_terminals,
  long*   n_points,
  Point*  pt,
  Point*  sorted_terms,
  long*   parent
)
{
  long   i, j, u, v, n_useless_stnr;
  long   n_stnr = (*n_points) - n_terminals;
  Point* stnr = pt + n_terminals;
  Point  tmp;

  /* 
    remove duplicate Steiner points
    and
    make sure Steiner points don't collide with terminals,
    assuming terminals don't collide with each other
    and that they are already in sorted order
    added by royj
  */ 

  for( i = 0;  i < n_stnr/2;  i++ )
  {
    j = unif_rand( n_stnr );
    tmp = stnr[i];  stnr[i] = stnr[j];  stnr[j] = tmp;
  }
  qsort( stnr, n_stnr, sizeof(Point), compare_points );

#ifdef DEBUG
    assert( is_sorted( stnr, n_stnr, sizeof(Point), compare_points ) );
#endif

/*
  u = (*n_points) - 1;
  while( u >= n_terminals )
  {
    if( (pt[u].x == pt[u-1].x) && (pt[u].y == pt[u-1].y) )  
    {
      pt[u] = pt[--(*n_points)]; 
    }
    u--;
  }
*/

  i = n_terminals - 1;
  j = (*n_points) - 1;
  while(i >= 0 && j >= n_terminals)
  {
    if( (j > n_terminals) && (pt[j].x == pt[j-1].x) && (pt[j].y == pt[j-1].y) )
    {
      pt[j] = pt[--(*n_points)];
      --j;
    }
    else
    {
      int comp = compare_points(&sorted_terms[i] , &pt[j]);
      if( comp == -1 ) /* sorted_terms[i] is smaller than pt[j] */
      {
        --j;
      }
      else if( comp == 0 )
      {
        pt[j] = pt[--(*n_points)];
        --j;
      }
      else /* comp == +1, sorted_terms[i] is bigger than pt[j] */
      {
        --i;
      }
    }
  }

  n_useless_stnr = UNDEFINED;
  while( n_useless_stnr != 0 )
  {
    mst2( *n_points, pt, parent );

    /** compute tree degrees **/
    degree[0] = 0;
    for( v = 1;  v < *n_points;  v++ )  { degree[v] = 1; }
    for( v = 1;  v < *n_points;  v++ )  { degree[parent[v]]++; }

    /** recursively remove edges incident to Steiner leaves **/
    for( v = n_terminals;  v < *n_points;  v++ ) {
      u = v; 
      while( (degree[u] == 1) && (u >= n_terminals) ) {
        degree[parent[u]]--;  degree[u]--;
        u = parent[u];
      }
    }

    /** remove isolated and degree-two Steiner points **/
    n_useless_stnr = 0;
    for( u = n_terminals;  u < *n_points;  u++ )
    {
      if( (degree[u] == 0) || (degree[u] == 2) ) 
      {
#ifdef DEBUG2
            printf( "delete stnr at (%f,%f)\n",
                    pt[u].x,
                    pt[u].y );
#endif
        pt[u] = pt[--(*n_points)];  
        n_useless_stnr++; 
      }
    }
  }
}

}

/****************************************************************************/
/****************************************************************************/

