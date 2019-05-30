#include  <stdlib.h>
#include  <stdio.h>
#include  <math.h>
#include  <assert.h>
#include  <string.h>
#include  "global.h"
#include  "mst2.h"
#include  "triples.h"
#include  "dist.h"
#include  "err.h"
#include  "unixtimer.h"
#include  "random.h"

namespace fastSteiner
{

/* 
  arrays allocated as globals for persistency purposes
  (to be reused from one call to another)
*/
long     max_n_triples = 0;
Triple*  triple        = (Triple*)NULL;
long*    sorted_stnr   = (long*)NULL;
long     max_n_edges   = 0;
Edge*    edge;
Edge*    edge2;


/****************************************************************************/
/****************************************************************************/

void  stnr1_package_init( long  max_n_points, long  flags )
{
  long  max1 = (long) (4*max_n_points);

  mst2_package_init( max_n_points );
  gain_package_init( max_n_points );
  triple_package_init( max_n_points );

  if( max_n_triples < max1 )
  {
    max_n_triples  = max1;
    //triple  = (Triple*) realloc( (void*)triple, (size_t)max_n_triples*sizeof(Triple) );   
    Triple* tmp_triple= static_cast<Triple *>( realloc( (void*)triple, (size_t)max_n_triples*sizeof(Triple) ) );
    if(tmp_triple == NULL) {
      free(triple);
      err_exit( "Cannot allocate memory triple!" );
    } else {
      triple = tmp_triple;
    }
  }
  if( max_n_edges < max_n_points )
  {
    //edge    = (Edge*) realloc( (void*)edge, (size_t)max_n_points*sizeof(Edge) );
    //edge2   = (Edge*) realloc( (void*)edge2, (size_t)max_n_points*sizeof(Edge) );
    //sorted_stnr = (long*) realloc( (void*)sorted_stnr, (size_t)max_n_points*sizeof(long) );
    Edge* tmp_edge= static_cast<Edge *>( realloc( (void*)edge, (size_t)max_n_points*sizeof(Edge) ) );
    if(tmp_edge == NULL) {
      free(edge);
      err_exit( "Cannot allocate memory edge!" );
    } else {
      edge = tmp_edge;
    }
    Edge* tmp_edge2= static_cast<Edge *>( realloc( (void*)edge2, (size_t)max_n_points*sizeof(Edge) ) );
    if(tmp_edge2 == NULL) {
      free(edge2);
      err_exit( "Cannot allocate memory edge2!" );
    } else {
      edge2 = tmp_edge2;
    }
    long* tmp_sorted_stnr= static_cast<long *>( realloc( (void*)sorted_stnr, (size_t)max_n_points*sizeof(long) ) );
    if(tmp_sorted_stnr == NULL) {
      free(sorted_stnr);
      err_exit( "Cannot allocate memory sorted_stnr!" );
    } else {
      sorted_stnr = tmp_sorted_stnr;
    }
    max_n_edges = max_n_points;
  }

  if( !triple || !edge || !edge2 || !sorted_stnr )
  {
    err_exit( "Cannot allocate memory in stnr1_package_init!" );
  }  

}

/****************************************************************************/
/****************************************************************************/

void  stnr1_package_done()
{
  mst2_package_done();
  triple_package_done();
  gain_package_done();

  if( triple )  { free(triple);   triple  = (Triple*)NULL;  }
  if( edge  )  { free( (void*)edge);   edge  = (Edge*)NULL; }
  if( edge2 ) { free( (void*)edge2);   edge2 = (Edge*)NULL; }
  if( sorted_stnr ) { free( (void*)sorted_stnr);  sorted_stnr = (long*)NULL; }

  max_n_triples = 0;
  max_n_edges   = 0;
}  

/***************************************************************************/
/***************************************************************************/
/*
  comparison functions for use in quicksort
*/

static  int compare_triples_by_gain
(
  const void*  t1,
  const void*  t2
) 
{
  double  diff = ((Triple*)t2)->gain - ((Triple*)t1)->gain;

  return( diff < 0 ? -1 : (diff > 0 ? 1 : ((Triple*)t1)->id - ((Triple*)t2)->id ) );   
}

/****************************************************************************/
/****************************************************************************/
/*
   apply triples in the given order, return total gain
*/
inline double  apply_triples
(
  long*    n_points,
  long     max_n_points,
  Point*   pt, 
  long*    n_triples,
  long     n_edges,
  long*    round_new_stnr,
  long     max_stnr_per_round,
  long*    phase_new_stnr,
  long     max_stnr_per_phase
)
{
  long     i, e0, e1;
  double   tot_gain = 0;
  Triple*  t;


  for( i = 0;  i < n_edges;  i++ )  
  {
    edge[i].free = TRUE; 
  }

  for( i = 0;  i < *n_triples;  i++ )
  {
    t  = triple + i;
    e0 = t->e[0];  e1 = t->e[1];

    if( edge[e0].free && edge[e1].free )
    {
#ifdef DEBUG
      assert( edge[e0].len >= t->gain );
      assert( edge[e1].len >= t->gain );
      assert( t->gain > 0 );
#endif
#ifdef DEBUG2
      printf( "free triple (%ld,%ld,%ld,gain=%.1f idx=%ld)\n",
               t->pt[0], t->pt[1], t->pt[2], t->gain, i );
#endif
      edge[e0].pt1 = t->pt[ static_cast<int>(t->repl[0][0]) ]; 
      edge[e0].pt2 = t->pt[ static_cast<int>(t->repl[0][1]) ];
      edge[e1].pt1 = t->pt[ static_cast<int>(t->repl[1][0]) ];
      edge[e1].pt2 = t->pt[ static_cast<int>(t->repl[1][1]) ];

      edge[e0].len = edge[e1].len = 0;
      tot_gain += t->gain;
      t->gain = -1;

      edge[e0].free = edge[e1].free = FALSE;
      pt[*n_points].x = t->stnr_x;
      pt[*n_points].y = t->stnr_y;

#ifdef DEBUG2
      printf( "insert stnr at (%f,%f)\n", 
              pt[*n_points].x, 
              pt[*n_points].y );
#endif

      (*phase_new_stnr)++;  (*round_new_stnr)++;  (*n_points)++;
      if( (*round_new_stnr >= max_stnr_per_round) || 
          (*phase_new_stnr >= max_stnr_per_phase) )  { break; }
      if( *n_points >= max_n_points )
      {
        err_exit( "MAX_NUM_POINTS exceeded!" );
      } 
    }
  }

  i = 0;  
  while( i < *n_triples )
  {
    if( triple[i].gain < 0 ) { triple[i] = triple[--(*n_triples)]; }
    else { i++; }
  }

  return  tot_gain;
}


/****************************************************************************/
/****************************************************************************/
/*
*/
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
)
{
  long      i, j;
  long      n_terminals, n_triples;
  long      n_edges, phase_number;
  long      phase_new_stnr, round_new_stnr;
  double    mst_len, len, old_len;
  Triple    tmp;
  Edge*     e;
  Point*    sorted_terms;

  /*
    sort terms for use later
    added by royj
  */

  sorted_terms = (Point*)calloc( *n_points, sizeof(Point));
  for( i = 0; i < *n_points; ++i )
  {
    sorted_terms[i] = pt[i];
  }
  qsort( sorted_terms, *n_points, sizeof(Point), compare_points );

  /*
    reallocate arrays, if needed 
  */
  stnr1_package_init( *n_points, flags ); 

  n_terminals = (*n_points);
  (*n_rounds) = (*n_phases) = 0;   round_new_stnr = UNDEFINED;  

  /*
     Compute mst over terminals
  */

  mst2( n_terminals, pt, parent );   

  mst_len = 0.0;
  for( i = 1;  i < (*n_points);  i++ )
  {
    mst_len += dist( pt[i], pt[parent[i]] );
  }

  len = mst_len;

  /****************************************************************
    Main loop: in each round we compute an MST and a set of O(n) 
    empty triples, then select a maximal set of compatible triples 
    with positive gain, add the corresponding Steiner points to the 
    set of terminals
  *****************************************************************/

  do
  {
    round_new_stnr = 0;
    (*n_rounds)++;
    old_len = len;

#ifdef DEBUG2
    for( i = 1;  i < *n_points;  i++ )
    {
      printf( "%ld %ld (%f,%f) -> (%f,%f)   %f\n",
              i, parent[i],
              pt[i].x, pt[i].y,
              pt[parent[i]].x, pt[parent[i]].y,
              dist( pt[i], pt[parent[i]] ) );
    }
#endif

    /* 
       setup edge array and build the auxiliary gain-computation datastructures
    */

    for( i = 1, e = edge;  i < (*n_points);  i++, e++ )
    {
       e->pt1  = e->id = i;
       e->pt2  = parent[i];
       e->len  = dist( pt[i], pt[parent[i]] );
       e->free = TRUE;
    }
    n_edges = (*n_points) - 1;
    preprocess_edges( n_edges, edge, edge2, TRUE );

    /*
      get list of empty tree triples with positive gain
    */
    collect_triples( *n_points, pt, &n_triples, max_n_triples, triple, edge );

    if( flags & PRINT_ROUNDS )
    {
      printf( "\nROUND# %2ld ", (*n_rounds) );
      printf( "NUM_POINTS: %7ld ", (*n_points) );
      printf( "NUM_TRIPLES: %10ld ", n_triples );
      printf( "TRIPL_TIME: %.2f ", cpu_seconds() );
      printf( "ROUND_START_LEN: %8.0f ", len );
      printf( "ROUND_START_GAIN: %5.3f ", ((mst_len - len)*100.0) / mst_len );
    }
    if( flags & PRINT_PHASES ) { printf( "\n" ); }


    phase_number = 0;  phase_new_stnr = UNDEFINED;

    /************************************************************** 
      Inner loop: repeatedly find and apply  maximal sets of compatible 
      triples using an (iterated batched) greedy order
    ***************************************************************/

    do
    {
      phase_number++;  (*n_phases)++;  phase_new_stnr = 0;

      if( flags & PRINT_PHASES )
      {
        printf( "PHASE# %2ld ",  phase_number );
        printf( "NUM_TRIPLES: %6ld ", n_triples );
      }


      for( i = 0;  i < n_triples/2;  i++ )
      {
        j = unif_rand(n_triples);
        tmp = triple[i];  triple[i] = triple[j];  triple[j] = tmp;
      }
      qsort( triple, n_triples, sizeof(Triple), compare_triples_by_gain );

#ifdef DEBUG
      assert( is_sorted( triple, n_triples, 
                         sizeof(Triple), compare_triples_by_gain ) );
#endif

      len -= apply_triples( n_points, max_n_points, pt, &n_triples, n_edges, 
                            &round_new_stnr, max_stnr_per_round, 
                            &phase_new_stnr, max_stnr_per_phase );


      if( flags & PRINT_PHASES )
      {
        printf( "PHASE_NEW_STNR: %6ld ", phase_new_stnr );
        printf( "PHASE_NEW_LEN: %8.0f ", len );
        printf( "PHASE_NEW_GAIN: %5.3f ", ((mst_len - len)*100.0) / mst_len );
        printf( "PHASE_TIME: %.2f\n", cpu_seconds() );
      }

      /*
         rebuild auxiliary gain-computation datastructures and remove negative 
         gain triples
      */
      if( n_triples > 0)
      {
        for( i = 0;  i < n_edges;  i++ )  { edge[i].free = TRUE; }
        preprocess_edges( n_edges, edge, edge2, FALSE );
        remove_negative_gain_triples( &n_triples, triple, edge );
      }

    } while( (phase_number < max_phases_per_round) &&
             (round_new_stnr < max_stnr_per_round) && 
             (n_triples > 0) );  

    /************************************************************** 
      End of inner loop
    ***************************************************************/
    
    if( (flags & PRINT_ROUNDS) && !(flags & PRINT_PHASES) )
    {
      printf( "ROUND_STNR: %6ld ", round_new_stnr );
      printf( "ROUND_END_LEN: %8.0f ", len );
      printf( "ROUND_END_GAIN: %5.3f ", ((mst_len - len)*100.0) / mst_len );
      printf( "ROUND_TIME: %.2f\n", cpu_seconds() );
    }

    /*
       Compute mst over terminals and steiner points, recursively
       deleting steiner leaves
    */
      
    if( round_new_stnr > 0 )
    {
      reduced_mst2( n_terminals, n_points, pt, sorted_terms, parent );
    
      len = 0.0;
      for( i = 1;  i < (*n_points);  i++ )
      {
        len += dist( pt[i], pt[parent[i]] );
      }
    }
     
  } while( ((*n_rounds) < max_rounds)  && ( len < (1.0-cut_off)*old_len ) );

  /************************************************************** 
    End of main loop
  ***************************************************************/

  free(sorted_terms);    

  return  len;
}

}

/****************************************************************************/
/****************************************************************************/

