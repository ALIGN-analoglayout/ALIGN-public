#include  <stdlib.h>
#include  <assert.h>
#include  <math.h>
#include  <string.h>
#include  "global.h"
#include  "random.h"
#include  "dist.h"
#include  "err.h"

namespace fastSteiner
{

extern Metric metric;

/*
   rotation coefficients 
*/
long   coeff[4][4] = {
                       { 1,  0,  0,  1},   
                       {-1,  0,  0,  1},   
                       { 1,  0,  0, -1},   
                       {-1,  0,  0, -1},   
                     };

#define  rotated_x( q, xx, yy )  ( coeff[q][0]*(xx) + coeff[q][1]*(yy) )
#define  rotated_y( q, xx, yy )  ( coeff[q][2]*(xx) + coeff[q][3]*(yy) )

/***************************************************************************/
/***************************************************************************/
/* 
  gain-related data structures and functions
*/
typedef  struct node_struct
         {
           long  e;
           long  p;
         } Node;

long   max_size_gain_arrays = 0;
Node*  node;

/***************************************************************************/
/*
  macros
*/

#define   e(i)   (node[i].e)
#define   p(i)   (node[i].p)
#define   edge_length(e)  (edge[e].len)

/***************************************************************************/
/*
  resize the auxiliary arrays to the specified size
*/

void  gain_package_init( long  n )
{
  if( max_size_gain_arrays < n )
  {
    node = (Node*) realloc( (void*)node,  (size_t)2*n*sizeof(Node) );
 
    if( !node )
    {
      err_exit( "Cannot allocate memory in triple_package_init!" );
    }
    max_size_gain_arrays = n; 
  }
} 

/***************************************************************************/
/*
  free memory used by auxiliary arrays
*/
   
void  gain_package_done()
{
  max_size_gain_arrays = 0;
  if( node )   { free( (void*)node );   node = (Node*)NULL; }
}


/***************************************************************************/
/*
  comparison function for use in quicksort 
*/

static  int compare_edge
( 
  const void*  e1, 
  const void*  e2 
)
{
  double diff = ((Edge*)e1)->len - ((Edge*)e2)->len;

  return( diff < 0 ? -1 : (diff > 0 ? 1 : ((Edge*)e1)->id - ((Edge*)e2)->id ) );
}

/***************************************************************************/
/* 
*/
void  preprocess_edges
(
  long   n_edges,
  Edge*  edge,
  Edge*  edge2,
  long   unsorted
)
{
  long  i, j, pt1, pt2, new_node;  
  long  n_points = n_edges + 1;
  Edge  tmp;

  for( i = 0;  i < n_points;  i++ ) {  p(i) = UNDEFINED; }

  new_node = n_points;


  /*
    sort the edges by length
  */

  if( unsorted )
  {
    for( i = 0;  i < n_edges/2;  i++ )
    {
      j = unif_rand(n_edges);
      tmp = edge[i];  edge[i] = edge[j];  edge[j] = tmp;
    }
    qsort( edge, n_edges, sizeof(Edge), compare_edge );

#ifdef DEBUG
    assert( is_sorted( edge, n_edges, sizeof(Edge), compare_edge ) );
#endif
  }

  else   /* edge array already sorted except for zero lengths */
  {
    for( i = 0;  i < n_edges;  i++ )  {  edge2[i] = edge[i]; }

    j = 0;
    for( i = 0;  i < n_edges;  i++ )  
    {
      if( edge2[i].len == 0 )  { edge[j++] = edge2[i]; }
    }
    for( i = 0;  i < n_edges;  i++ )  
    {
      if( edge2[i].len > 0 )  { edge[j++] = edge2[i]; }
    }

#ifdef DEBUG
    assert( j == n_edges );
#endif
  }


  for( i = 0;  i < n_edges;  i++ )
  {
    pt1 = edge[i].pt1;
    pt2 = edge[i].pt2;

    while( TRUE )
    {
      if( p(pt1) == UNDEFINED )
      {
        if( p(pt2) == UNDEFINED )
        {

#ifdef DEBUG
          assert( new_node < 2*n_points );
#endif

          p( pt1 ) = p( pt2 ) = new_node;
          e( pt1 ) = e( pt2 ) = i;
          p( new_node++ ) = UNDEFINED;
          break;
        }
        else
        {
          p( pt1 ) = p( pt2 );
          e( pt1 ) = i;
          break;
        }
      }
      else if( p(pt2) == UNDEFINED )
      {
        p( pt2 ) = p( pt1 );
        e( pt2 ) = i;
        break;
      }
      else
      {
        pt1 = p( pt1 ); 
        pt2 = p( pt2 );
      }
    }
  }
}

/***************************************************************************/
/* 
*/
inline long  longest_path_edge( long i, long j )
{
  long  e;

#ifdef DEBUG
  assert( (0 <= i) && (i < max_size_gain_arrays) );
  assert( (0 <= j) && (j < max_size_gain_arrays) );
#endif

  e = e(i);

  while( i != j )
  {
    if( e(i) > e )  e = e(i);
    if( e(j) > e )  e = e(j);
    i = p(i);  j = p(j);
  }

  return e;
}

/***************************************************************************/
/*
*/
inline void  set_triple_gain
(
  Triple*  t, 
  Edge*  edge 
)
{
#ifdef DEBUG
  assert( t && (t->length > 0) );
#endif

    t->e[0] = longest_path_edge( t->pt[0], t->pt[1] ); 
    t->repl[0][0] = 0;  t->repl[0][1] = 1;  
    t->e[1] = longest_path_edge( t->pt[1], t->pt[2] );
    if( (t->e[0]) == (t->e[1]) ) 
    {
      t->e[1] = longest_path_edge( t->pt[0], t->pt[2] );
      t->repl[1][0] = 0;  t->repl[1][1] = 2;  
    }
    else
    {
      t->repl[1][0] = 1;  t->repl[1][1] = 2;  
    }

    t->gain = edge_length( t->e[0] ) + edge_length( t->e[1] ) - t->length;
}

/***************************************************************************/
/*
*/
void  remove_negative_gain_triples
(
  long*    n_triples,
  Triple*  triple,
  Edge*    edge
)
{
  long     i;

  i = 0;
  while( i < (*n_triples) )
  {
    set_triple_gain( triple + i, edge );
    if( triple[i].gain <= 0 ) 
    {
      triple[i] = triple[--(*n_triples)];
    }
    else
    {
      i++;
    }
  }
}


/***************************************************************************/
/***************************************************************************/
/* 
  triple-related data structures and functions
*/

/*
  Auxiliary arrays are allocated as globals
*/
long    max_size_aux_arrays  = 0;
Point*  rotated       = (Point*)NULL;
long*   x_sorted      = (long*)NULL;
long*   y_sorted      = (long*)NULL;
long*   d1_sorted     = (long*)NULL;
long*   d2_sorted     = (long*)NULL;
long*   aux1          = (long*)NULL;  
long*   aux2          = (long*)NULL;  
long*   aux3          = (long*)NULL;  
long*   aux4          = (long*)NULL;  

/***************************************************************************/
/*
  Macros
*/
#define   x(i)  (rotated[i].x)
#define   y(i)  (rotated[i].y)

/*
   break all ties in coordinates according to point indices 
*/

#define   LESS_X(i,j)  ( x(i)== x(j) ?  (i < j) : (x(i) < x(j)) )
#define   LESS_Y(i,j)  ( y(i)== y(j) ?  (i < j) : (y(i) < y(j)) )
#define   LESS_D1(i,j)  ( (x(i)+y(i)) == (x(j)+y(j)) ?  (i < j) : \
                                   ( (x(i)+y(i)) < (x(j)+y(j)) ) )
#define   LESS_D2(i,j)  ( (y(i)-x(i)) == (y(j)-x(j)) ?  (i < j) : \
                                   ( (y(i)-x(i)) < (y(j)-x(j)) ) )

/* 
  following pairs of macros reuse auxiliary arrays since they are 
  never used at the same time
*/

#define  leftmost_low_right(i)  (aux1[i])
#define  rightmost_low_left(i)  (aux2[i])

#define  highest_low_left(i)    (aux1[i])
#define  lowest_high_left(i)    (aux2[i])

#define  highest_low_right(i)   (aux1[i])
#define  lowest_high_right(i)   (aux2[i])

#define  leftmost_high_right(i) (aux1[i])
#define  rightmost_high_left(i) (aux2[i])

#define  is_stripe_end(i)   (aux3[i])
#define  highest(i)         (aux4[i])
#define  leftmost(i)        (aux4[i])

/***************************************************************************/
/*
   Save a triple (rotated in SE orientation) if has positive gain
*/
inline void  save_triple
(
  long      a, 
  long      b,
  long      c,
  long*     n_triples,
  long      max_n_triples,
  Triple*   triple, 
  Edge*     edge,
  long      q
)
{ 
  Triple*   t;
  Point     s[4];
  long      i, best_i;
  double    dx, dy, d1, d2, d3, len, best_len;

#ifdef  DEBUG
  assert( LESS_X(a,b) && LESS_X(b,c) && LESS_Y(b,c) && LESS_Y(c,a) );
#endif

#ifdef DEBUG2
      printf( "\nChecking triple (%f,%f) (%f,%f) (%f,%f)",
              rotated_x( q, x(a), y(a) ),  rotated_y( q, x(a), y(a) ), 
              rotated_x( q, x(b), y(b) ),  rotated_y( q, x(b), y(b) ), 
              rotated_x( q, x(c), y(c) ),  rotated_y( q, x(c), y(c) ) );
#endif

  if( (*n_triples) < max_n_triples )
  { 
    t         = triple + (*n_triples);
    t->pt[0]  = a;  t->pt[1] = b;  t->pt[2] = c;

    if( metric == RECTILINEAR )
    {
      t->length = x(c) - x(a) + y(a) - y(b);
      t->stnr_x = rotated_x( q, x(b), y(c) );
      t->stnr_y = rotated_y( q, x(b), y(c) );
      set_triple_gain( t, edge ); 
    }
    else
    {
#ifdef DEBUG
       assert( metric == OCTILINEAR );
#endif
      /*
        find the degree-2 point of the MST for the triple 
      */
      d1 = dist( rotated[b], rotated[c] );
      d2 = dist( rotated[a], rotated[c] );
      d3 = dist( rotated[a], rotated[b] );
      if( d1 > d2 ) 
      {
        if( d1 > d3 ) { s[0].x = x(a); s[0].y = y(a); }
        else          { s[0].x = x(c); s[0].y = y(c); }
      }
      else /* d2 >= d1 */
      {
        if( d2 > d3 ) { s[0].x = x(b); s[0].y = y(b); }
        else          { s[0].x = x(c); s[0].y = y(c); }
      }

      /*
         compute the 3 candidate steiner points
      */
      s[1].x = x(b);                    s[1].y = y(a) - ( x(b) - x(a) );
      s[2].x = x(a) + ( y(a) - y(c) );  s[2].y = y(c);
      dx = x(c) - x(b);  dy = y(c) - y(b); 
      if( dx < dy )  {  s[3].x = x(b);       s[3].y = y(c) - dx; }
      else           {  s[3].x = x(b) + dy;  s[3].y = y(c); }


      best_i = UNDEFINED;   best_len = INFTY;
      for( i = 0;  i < 4; i++ )
      {
        len = dist(s[i],rotated[a]) + dist(s[i],rotated[b]) + dist(s[i],rotated[c]);
        if( len < best_len )  { best_len = len;  best_i = i; }
      }

#ifdef DEBUG
       assert( best_i != UNDEFINED );
#endif
      if( best_i > 0 )
      {
        t->length = best_len; 
        t->stnr_x = rotated_x( q, s[best_i].x, s[best_i].y );
        t->stnr_y = rotated_y( q, s[best_i].x, s[best_i].y );
        set_triple_gain( t, edge );
      }
      else
      {
        t->gain = 0;  /* triple has zero or negative gain, ignore */
      }
    }

    if( t->gain > 0 )
    {
       t->id = (*n_triples)++;

#ifdef DEBUG2
      printf( "\nSaved triple (%f,%f) (%f,%f) (%f,%f) with stnr (%f,%f) and gain=%f",
              rotated_x( q, x(a), y(a) ),  rotated_y( q, x(a), y(a) ), 
              rotated_x( q, x(b), y(b) ),  rotated_y( q, x(b), y(b) ), 
              rotated_x( q, x(c), y(c) ),  rotated_y( q, x(c), y(c) ), 
              t->stnr_x, t->stnr_y, t->gain );
#endif
    }
  }
  else
  {
    err_exit( "max_n_triples exceeded!" );
  }
}

/***************************************************************************/
/*
  resize the auxiliary arrays to the specified size 
*/

void  triple_package_init( long  n )
{
  if( max_size_aux_arrays < n ) 
  {
    rotated   = (Point*) realloc( (void*)rotated,  (size_t)n*sizeof(Point) );
    x_sorted  = (long*)  realloc( (void*)x_sorted, (size_t)n*sizeof(long)  );
    y_sorted  = (long*)  realloc( (void*)y_sorted, (size_t)n*sizeof(long)  );
    d1_sorted = (long*)  realloc( (void*)d1_sorted,(size_t)n*sizeof(long)  );
    d2_sorted = (long*)  realloc( (void*)d2_sorted,(size_t)n*sizeof(long)  );
    aux1      = (long*)  realloc( (void*)aux1,     (size_t)n*sizeof(long)  );
    aux2      = (long*)  realloc( (void*)aux2,     (size_t)n*sizeof(long)  );
    aux3      = (long*)  realloc( (void*)aux3,     (size_t)n*sizeof(long)  );
    aux4      = (long*)  realloc( (void*)aux4,     (size_t)n*sizeof(long)  );

    if( !rotated || !x_sorted || !y_sorted || !d1_sorted || !d2_sorted ||
         !aux1 || !aux2 || !aux3 || !aux4 )
    {
      err_exit( "Cannot allocate memory in triple_package_init!" );
    }
    max_size_aux_arrays = n;
  }
}

/***************************************************************************/
/*
  free memory used by auxiliary arrays
*/

void  triple_package_done()
{
  max_size_aux_arrays = 0;
  if( rotated )   { free( (void*)rotated );   rotated = (Point*)NULL; }
  if( x_sorted )  { free( (void*)x_sorted );  x_sorted = (long*)NULL; }
  if( y_sorted )  { free( (void*)y_sorted );  y_sorted = (long*)NULL; }
  if( d1_sorted ) { free( (void*)d1_sorted ); d1_sorted = (long*)NULL;}
  if( d2_sorted ) { free( (void*)d2_sorted ); d2_sorted = (long*)NULL;}
  if( aux1 )      { free( (void*)aux1 );      aux1 = (long*)NULL;     }
  if( aux2 )      { free( (void*)aux2 );      aux2 = (long*)NULL;     }
  if( aux3 )      { free( (void*)aux3 );      aux3 = (long*)NULL;     }
  if( aux4 )      { free( (void*)aux4 );      aux4 = (long*)NULL;     }
}

/***************************************************************************/
/*
  comparison function for use in quicksort 
*/

static  int compare_d1
( 
  const void*  i1, 
  const void*  i2 
)
{
  long  j1 = *((long*)i1);
  long  j2 = *((long*)i2);
  if( LESS_D1(j1,j2) )  
    return -1;
  else 
    return +1;
}

/***************************************************************************/
/*
  collect SE-oriented triples with all points in 
    { d1_sorted[left], ..., d1_sorted[right-1] }  
  and at least one point in each of the sets 
    { d1_sorted[left], ..., d1_sorted[mid-1] } 
  and 
    { d1_sorted[mid], ..., d1_sorted[right-1] }
*/

void  se_combine
(
  long      left,
  long      mid,
  long      right,
  long*     n_triples,
  long      max_n_triples, 
  Triple*   triple, 
  Edge*     edge,
  long      q
)
{
  long  i, j, k, i1, i2, j1, k1, b, d, r;
 
#ifdef DEBUG
  assert( right - left > 0 );
#endif

  if( right - left >= 3 )
  {
    /********************************************************************
      collect triples of type 1, i.e., triples (d,r,b) with 
      r = leftmost_low_right(d) and b = highest among the points in 
      d1_sorted[left],..., d1_sorted[mid-1] with an x coordinate 
      between d and r 
    *********************************************************************/

    /*
       compute "leftmost point lower and to the right" for points 
       from d1_sorted[mid],..., d1_sorted[right-1]
    */
    for( i = mid; i < right; i++ )
    {
      leftmost_low_right( x_sorted[i] ) = UNDEFINED;
    }

    rightmost_low_left( x_sorted[mid] ) = UNDEFINED;
    for( i = mid; i < right-1; i++ )    /* ascending x order */
    {
      i1 = x_sorted[i];
      i2 = x_sorted[i+1];
      while( LESS_Y(i2,i1) )
      { 
        leftmost_low_right(i1) = i2;  
        i1 = rightmost_low_left(i1); 
        if( i1 == UNDEFINED )  break;
      }
      rightmost_low_left(i2) = i1;
    }
  
    /*
       mark stripe ends and initialize highest for each stripe end
    */
    for( i = mid; i < right; i++ )
    {
      i1 = x_sorted[i];
      is_stripe_end( i1 ) = FALSE;
      highest( i1 ) = UNDEFINED;
    }
    for( i = mid; i < right; i++ )
    {
      i1 = x_sorted[i];
      i2 = leftmost_low_right( i1 );
      if( i2 != UNDEFINED )
      {
        is_stripe_end( i1 ) = is_stripe_end( i2 ) = TRUE;
      }
    }

    /*
       compute highest point in each stripe
    */
    for( i = mid;  i < right;  i++ )
    {
      if( is_stripe_end(x_sorted[i]) ) break;
    }
    for( j = i+1;  j < right;  j++ )
    {
      if( is_stripe_end(x_sorted[j]) ) break;
    }
#ifdef DEBUG
    assert( ((i < right) && (j<right)) || ((i==right) && (j==i+1)) );
#endif

    if( j < right ) 
    {
      i1 = x_sorted[i];
      for( k = left;  k < mid;  k++ )
      {
        if( LESS_X(i1, x_sorted[k]) ) break; 
      }

      while( (j < right) && (k < mid) )
      {
        j1 = x_sorted[j];  
        k1 = x_sorted[k];

        if( LESS_X(k1, j1) )  /* k1 is in stripe between i1 and j1 */
        {
          if( (highest(i1) == UNDEFINED) || LESS_Y(highest(i1),k1) )
          {
            highest(i1) = k1;
          }
          k++; k1 = x_sorted[k];
        }
        else /* move to next stripe */
        {
          i = j;  i1 = j1;
          for( j = i+1;  j < right;  j++ )
          {
            if( is_stripe_end(x_sorted[j]) ) break;
          }
          j1 = x_sorted[j];
        }
      }
    }

    /*
       go over stripe ends in top-to-bottom order, collecting triples 
       and updating "highest"
    */
    for( i = right - 1;  i >= mid;  i-- )
    {
      i1 = y_sorted[i];
      if( (leftmost_low_right(i1) != UNDEFINED) && (highest(i1) != UNDEFINED) ) 
      {
        if( LESS_Y(highest(i1), leftmost_low_right(i1)) )
        {
          save_triple( i1, 
                       highest(i1), 
                       leftmost_low_right(i1),
                       n_triples, 
                       max_n_triples,
                       triple,
                       edge,
                       q
                     );
        }
        j1 = rightmost_low_left(i1);
        if( (j1 != UNDEFINED ) && 
            ( (highest(j1) == UNDEFINED) || LESS_Y(highest(j1),highest(i1)) ) )
        {
          highest(j1) = highest(i1);
        }
      }
    }

    /********************************************************************
      collect triples of type 2, i.e., triples (d,r,b) with 
      b = highest_low_left(r) and d = closest point to r (and b) among 
      points higher than r in d1_sorted[left],..., d1_sorted[mid-1] 
    *********************************************************************/

    /*
       compute "highest point lower and to the left" for points 
       from d1_sorted[mid],..., d1_sorted[right-1]
    */
    for( i = mid; i < right; i++ )
    {
      highest_low_left( y_sorted[i] ) = UNDEFINED;
    }

    lowest_high_left( y_sorted[right-1] ) = UNDEFINED;
    for( i = right - 1; i > mid; i-- )  /* descending y order */
    {
      i1 = y_sorted[i];
      i2 = y_sorted[i-1];
      while( LESS_X(i2,i1) )
      { 
        highest_low_left(i1) = i2;  
        i1 = lowest_high_left(i1); 
        if( i1 == UNDEFINED )  break;
      }
      lowest_high_left(i2) = i1;
    }
  
    /*
       now collect type 2 triples 
    */
    r = mid;       /* r is advanced in ascending y order */
    d = left;      /* d is advanced in ascending d2 order */
    while( (r < right) && (d < mid) )
    {
      if( highest_low_left(y_sorted[r]) == UNDEFINED )  { r++; }
      else if( LESS_Y(d2_sorted[d], y_sorted[r]) ) { d++; }
      else 
      { 
        save_triple( d2_sorted[d], 
                     highest_low_left(y_sorted[r]), 
                     y_sorted[r],
                     n_triples, 
                     max_n_triples,
                     triple,
                     edge,
                     q
                   );
        r++;
      }
    }

    /********************************************************************
      collect triples of type 3, i.e., triples (d,r,b) with 
      b = highest_low_right(d) and r = leftmost among the points in 
      d1_sorted[mid],..., d1_sorted[right-1] with an y coordinate 
      between d and b 
    *********************************************************************/

    /*
       compute "highest point lower and to the right" for points 
       from d1_sorted[left],..., d1_sorted[mid-1]
    */
    for( i = left; i < mid; i++ )
    {
      highest_low_right( y_sorted[i] ) = UNDEFINED;
    }

    lowest_high_right( y_sorted[mid-1] ) = UNDEFINED;
    for( i = mid - 1; i > left; i-- )    /* descending y order */
    {
      i1 = y_sorted[i];
      i2 = y_sorted[i-1];
      while( LESS_X(i1,i2) )
      { 
        highest_low_right(i1) = i2;  
        i1 = lowest_high_right(i1); 
        if( i1 == UNDEFINED )  break;
      }
      lowest_high_right(i2) = i1;
    }
  
    /*
       mark stripe ends and initialize leftmost for each stripe end
    */
    for( i = mid - 1; i >= left; i-- )
    {
      i1 = y_sorted[i];
      is_stripe_end( i1 ) = FALSE;
      leftmost( i1 ) = UNDEFINED;
    }
    for( i = mid - 1; i >= left; i-- )
    {
      i1 = y_sorted[i];
      i2 = highest_low_right( i1 );
      if( i2 != UNDEFINED )
      {
        is_stripe_end( i1 ) = is_stripe_end( i2 ) = TRUE;
      }
    }

    /*
       compute leftmost point in each stripe
    */
    for( i = mid - 1;  i >= left;  i-- )
    {
      if( is_stripe_end(y_sorted[i]) ) break;
    }
    for( j = i - 1;  j >= left;  j-- )
    {
      if( is_stripe_end(y_sorted[j]) ) break;
    }
#ifdef DEBUG
    assert( ((i >= left) && (j >= left)) || ((i==left-1) && (j==i-1)) );
#endif

    if( j >= left ) 
    {
      i1 = y_sorted[i];
      for( k = right - 1;  k >= mid;  k-- )
      {
        if( LESS_Y(y_sorted[k], i1) ) break; 
      }

      while( (j >= left) && (k >= mid) )
      {
        j1 = y_sorted[j];
        k1 = y_sorted[k];

        if( LESS_Y(j1, k1) )  /* k1 is in stripe between i1 and j1 */
        {
          if( (leftmost(i1) == UNDEFINED) || LESS_X(k1,leftmost(i1)) )
          {
            leftmost(i1) = k1;
          }
          k--; 
        }
        else /* move to next stripe */
        {
          i = j;  i1 = j1;
          for( j = i - 1;  j >= left;  j-- )
          {
            if( is_stripe_end(y_sorted[j]) ) break;
          }
        }
      }
    }

    /*
       go over the stripes, in left-to-right order, collecting triples 
       and updating "rightmost"
    */
    for( i = left;  i < mid;  i++ )
    {
      i1 = x_sorted[i];
      if( (highest_low_right(i1) != UNDEFINED) && (leftmost(i1) != UNDEFINED) ) 
      {
        if( LESS_X(highest_low_right(i1), leftmost(i1)) )
        {
          save_triple( i1, 
                       highest_low_right(i1),
                       leftmost(i1), 
                       n_triples, 
                       max_n_triples,
                       triple,
                       edge,
                       q
                     );
        }
        j1 = lowest_high_right(i1);
        if( (j1 != UNDEFINED ) && 
              ( (leftmost(j1) == UNDEFINED) || 
                LESS_X(leftmost(i1),leftmost(j1)) ) )
        {
          leftmost(j1) = leftmost(i1);
        }
      }
    }

    /********************************************************************
      collect triples of type 4, i.e., triples (d,r,b) with 
      r = leftmost_high_right(b) and d = closest point to b (and r) among 
      points to the left of b in d1_sorted[mid],..., d1_sorted[right-1] 
    *********************************************************************/

    /*
      compute "leftmost point higher and to the right" for points
      from d1_sorted[left],..., d1_sorted[mid-1]
    */
    for( i = left; i < mid; i++ )
    {
      leftmost_high_right( x_sorted[i] ) = UNDEFINED;
    }

    rightmost_high_left( x_sorted[left] ) = UNDEFINED;
    for( i = left; i < mid - 1; i++ )  /* ascending x order */
    {
      i1 = x_sorted[i];
      i2 = x_sorted[i+1];
      while( LESS_Y(i1,i2) )
      { 
        leftmost_high_right(i1) = i2;  
        i1 = rightmost_high_left(i1); 
        if( i1 == UNDEFINED )  break;
      }
      rightmost_high_left(i2) = i1;
    }

    /*
       now collect type 4 triples
    */  
    b = mid-1;    /* b is advanced in descending x order */
    d = mid;      /* d is advanced in ascending d2 order */
    while( (b >= left ) && (d < right) )
    {
      if( leftmost_high_right(x_sorted[b]) == UNDEFINED )  { b--; }
      else if( LESS_X(x_sorted[b], d2_sorted[d]) ) { d++; }
      else
      {
        save_triple( d2_sorted[d], 
                     x_sorted[b], 
                     leftmost_high_right(x_sorted[b]),
                     n_triples, 
                     max_n_triples,
                     triple,
                     edge,
                     q
                   );
        b--;
      }
    }

  }   /* if( right - left >= 3 ) */


  /********************************************************************
    merge the x-, y-, and d2-ascendingly sorted lists
  *********************************************************************/

  i = left;  j = mid;   k = left;
  while( (i < mid) && (j < right) )
  {
    if( LESS_X(x_sorted[i], x_sorted[j]) )
      { aux1[k++] = x_sorted[i++]; }
    else 
      { aux1[k++] = x_sorted[j++]; }
  }
  while( i < mid   ) {  aux1[k++] = x_sorted[i++]; }
  while( j < right ) {  aux1[k++] = x_sorted[j++]; }
  memcpy( (void*)(x_sorted+left),           /* destination */
          (void*)(aux1+left),               /* source      */
          (size_t)(right-left)*sizeof(long) /* number of bytes */ 
        );


  i = left;  j = mid;   k = left;
  while( (i < mid) && (j < right) )
  {
    if( LESS_Y(y_sorted[i], y_sorted[j]) )
      { aux1[k++] = y_sorted[i++]; }
    else 
      { aux1[k++] = y_sorted[j++]; }
  }
  while( i < mid   ) {  aux1[k++] = y_sorted[i++]; }
  while( j < right ) {  aux1[k++] = y_sorted[j++]; }
  memcpy( (void*)(y_sorted+left),           /* destination */
          (void*)(aux1+left),               /* source      */
          (size_t)(right-left)*sizeof(long) /* number of bytes */ 
        );

  i = left;  j = mid;   k = left;
  while( (i < mid) && (j < right) )
  {
    if( LESS_D2(d2_sorted[i], d2_sorted[j]) )
      { aux1[k++] = d2_sorted[i++]; }
    else 
      { aux1[k++] = d2_sorted[j++]; }
  }
  while( i < mid   ) {  aux1[k++] = d2_sorted[i++]; }
  while( j < right ) {  aux1[k++] = d2_sorted[j++]; }
  memcpy( (void*)(d2_sorted+left),          /* destination */
          (void*)(aux1+left),               /* source      */
          (size_t)(right-left)*sizeof(long) /* number of bytes */ 
        );

}


/***************************************************************************/
/*
  collect SE-oriented triples among points indexed by 
  { sorted_d1[left],..., sorted_d1[right-1] }
*/

void  collect_se_triples
(
  long      left,
  long      right,
  long*     n_triples,
  long      max_n_triples,
  Triple*   triple, 
  Edge*     edge,
  long      q
)
{
  long   mid;

#ifdef DEBUG
  assert( right - left >= 2);
#endif

  /* 
    although triples can be found only among >= 3 points, need recursive calls 
    for two point subproblems to get the x-, y-, and d2-sorted lists
  */
  mid = (left + right) / 2;
  if( mid - left  >= 2 )  
  {
    collect_se_triples( left, mid, n_triples, max_n_triples, triple, edge, q );
  }
  if( right - mid >= 2 )
  {
    collect_se_triples( mid, right, n_triples, max_n_triples, triple, edge, q ); 
  }
  se_combine( left, mid, right, n_triples, max_n_triples, triple, edge, q );   

}

/***************************************************************************/
/*
  collect all empty tree triples
*/

void  collect_triples
(
  long      n_pts,
  Point*    pt,
  long*     n_triples,
  long      max_n_triples,
  Triple*   triple,
  Edge*     edge
)
{
  long      i, j, q, tmp;

  (*n_triples) = 0;

  if( n_pts >= 3 )
  {
    /*
       rotate each quadrant into first, then collect SE-oriented triples 
    */
    for( q = 0;  q < 4;  q++ ) 
    {
      for( i = 0;   i < n_pts;   i++ )
      {
        rotated[i].x = rotated_x( q, pt[i].x, pt[i].y );
        rotated[i].y = rotated_y( q, pt[i].x, pt[i].y );
        d1_sorted[i] = i;
      }
      /*
        sort points along first diagonal
      */

      for( i = 0;  i < n_pts/2;  i++ )
      {
        j = unif_rand(n_pts);
        tmp = d1_sorted[i];  d1_sorted[i] = d1_sorted[j];  d1_sorted[j] = tmp;
      }
      qsort( d1_sorted, n_pts, sizeof(long), compare_d1 );  

#ifdef DEBUG
    assert( is_sorted( d1_sorted, n_pts, sizeof(long), compare_d1 ) );
#endif
     
      /*
        all other directions are sorted by the recursive calls
      */
      for( i = 0;   i < n_pts;   i++ )
      {
        x_sorted[i] = y_sorted[i] = d2_sorted[i] = d1_sorted[i];
      }

      collect_se_triples( 0, n_pts, n_triples, max_n_triples, triple, edge, q );

#ifdef DEBUG2
      printf("\n------------- end quadrant %ld ----------\n", q);
#endif
    }
  }

}

}

/***************************************************************************/
/***************************************************************************/

