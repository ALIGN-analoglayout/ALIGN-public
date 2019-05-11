#include  <stdio.h>
#include  <stdlib.h>
#include  <string.h>
#include  <assert.h>
#include  "global.h"
#include  "random.h"
#include  "mst2.h"
#include  "stnr1.h"
#include  "dist.h"
#include  "err.h"
#include  "unixtimer.h"

namespace fastSteiner
{
Metric  metric = DEFAULT_METRIC;
}

using namespace fastSteiner;

/****************************************************************************/

void   print_usage( char*  cmd )
{
  fprintf( stderr, "Usage: %s ", cmd );
  fprintf( stderr, "[-rectilinear | -octilinear] " );
  fprintf( stderr, "[-no_results] " );
  fprintf( stderr, "[-print_tree] " );
  fprintf( stderr, "[-print_rounds] " );
  fprintf( stderr, "[-print_phases] " );
  fprintf( stderr, "[-max_rounds N] " );
  fprintf( stderr, "[-max_phases_per_round N] " );
  fprintf( stderr, "[-max_stnr_per_round N] " );
  fprintf( stderr, "[-max_stnr_per_phase N] " );
  fprintf( stderr, "[-cut_off 0.N] " );
  fprintf( stderr, "[-timed_stnr_runs N] " );
  fprintf( stderr, "[-timed_mst_runs N] " );
  fprintf( stderr, "[-seed N] < INPUT_FILE\n" );
}

/****************************************************************************/

int  main
(
  int      argc,
  char**   argv
)
{
  long    i;
  long    n_terminals, n_points, max_points;
  long    n_rounds, n_phases;
  long    flags                = DEFAULT_FLAGS;
  long    max_rounds           = DEFAULT_MAX_ROUNDS;
  long    max_phases_per_round = DEFAULT_PHASES_PER_ROUND;
  long    max_stnr_per_round   = DEFAULT_STNR_PER_ROUND;
  long    max_stnr_per_phase   = DEFAULT_STNR_PER_PHASE;
  long    timed_stnr_runs      = DEFAULT_TIMED_STNR_RUNS;
  long    timed_mst_runs       = DEFAULT_TIMED_MST_RUNS;
  long    seed                 = DEFAULT_SEED;
  double  cut_off              = DEFAULT_CUT_OFF;

  double  mst_len, stnr_len;
  double  mst_time, stnr_time;
  Point*  pt;
  long*   parent;

  /* 
    read command line parameters
  */
  for( i = 1; i < argc; i++) 
  {
    if(!strncmp(argv[i], "-rectilinear", strlen("-rectilinear"))) 
    {
      metric = RECTILINEAR;
    }
    else if(!strncmp(argv[i], "-octilinear", strlen("-octilinear"))) 
    {
      metric = OCTILINEAR;
    }
    else if(!strncmp(argv[i], "-no_results", strlen("-no_results")))
    {
      flags &= ALL_FLAGS - PRINT_RESULTS;
    }
    else if(!strncmp(argv[i], "-print_tree", strlen("-print_tree")))
    {
      flags |= PRINT_TREE;
    }
    else if(!strncmp(argv[i], "-print_phases", strlen("-print_phases"))) 
    {
      flags |= PRINT_PHASES;
    }
    else if(!strncmp(argv[i], "-print_rounds", strlen("-print_rounds"))) 
    {
      flags |= PRINT_ROUNDS;
    }
    else if(!strncmp(argv[i], "-max_rounds", strlen("-max_rounds"))) 
    {
      max_rounds = atol(argv[++i]);
    }
    else if(!strncmp(argv[i], "-max_phases_per_round", strlen("-max_phases_per_round"))) 
    {
      max_phases_per_round = atol(argv[++i]);
    }
    else if(!strncmp(argv[i], "-max_stnr_per_round", strlen("-max_stnr_per_round"))) 
    {
      max_stnr_per_round = atol(argv[++i]);
    }
    else if(!strncmp(argv[i], "-max_stnr_per_phase", strlen("-max_stnr_per_phase"))) 
    {
      max_stnr_per_phase = atol(argv[++i]);
    }
    else if(!strncmp(argv[i], "-cut_off", strlen("-cut_off"))) 
    {
      cut_off = atof(argv[++i]);
    }
    else if(!strncmp(argv[i], "-timed_stnr_runs", strlen("-timed_stnr_runs"))) 
    {
      timed_stnr_runs = atol(argv[++i]);
    }
    else if(!strncmp(argv[i], "-timed_mst_runs", strlen("-timed_mst_runs"))) 
    {
      timed_mst_runs = atol(argv[++i]);
    }
    else if(!strncmp(argv[i], "-seed", strlen("-seed"))) 
    {
      seed = atol(argv[++i]);
    }

    else /* unrecognized parameter */
    {
      print_usage( argv[0] );
      return  -1;
    }
  }


  init_rand( seed );

  /* 
    allocate memory and read terminals
  */
  if( scanf( "%ld\n", &n_terminals ) != 1 )
  {
    err_exit( "Missing number of points" );
  }

  if( n_terminals <= 0 ) return  -1;

  max_points = 4 * n_terminals;
  pt     = (Point*)calloc( max_points, sizeof(Point) );
  parent = (long*)calloc( max_points, sizeof(long) );

  if( !pt || !parent )
  {
    err_exit( "Cannot allocate memory in main()!" );
  }

  for( i = 0;  i < n_terminals;  i++ )
  {
    if( scanf( "%lf %lf\n", &(pt[i].x), &(pt[i].y) ) != 2 )
    {
      err_exit( "Missing point coordinates!" );
    } 
  }

  /********************************** 
    more initilizations (not timed)
  */

  mst2_package_init( n_terminals );

  /********************************** 
    time 'timed_mst_runs' MST computations 
  */

  start_timer();
  for( i = 0;  i < timed_mst_runs;  i++ )
  { 
    mst2( n_terminals, pt, parent );
  }
  mst_time = cpu_seconds();
    
  mst_len = 0.0;
  for( i =1;  i < n_terminals;  i++ )
  { 
    mst_len += dist( pt[i], pt[parent[i]] );
  }


  stnr_len = INFTY;  stnr_time = 0;

  if( timed_stnr_runs > 0 )
  {

    stnr1_package_init( max_points, flags );

    /********************************** 
      time 'timed_stnr_runs' tree computations 
    */

    start_timer();
    for( i = 0;  i < timed_stnr_runs;  i++ )
    { 
      n_points = n_terminals;
      stnr_len = stnr1( &n_points, max_points, pt, parent, &n_rounds, max_rounds,
             &n_phases, max_phases_per_round, max_stnr_per_round, 
             max_stnr_per_phase, cut_off, flags );

    }
    stnr_time = cpu_seconds();
  } 

  /********************************** 
    print results 
  */

  if( flags & PRINT_TREE )
  {
    if( timed_stnr_runs < 1 ) { n_points = n_terminals; }
    for( i = 1;  i < n_points;  i++ )
    {
      printf( "%ld (%f, %f) -> (%f, %f)   %f\n",
              i, //parent[i], 
              pt[i].x, pt[i].y,
              pt[parent[i]].x, pt[parent[i]].y,
	      dist( pt[i], pt[parent[i]] ) );
    }
  }  

  if( flags & PRINT_RESULTS )
  {
    printf( "NUM_TERM: %6ld ", n_terminals );
    printf( "NUM_STNR: %6ld ", n_points - n_terminals );
    printf( "MST_LEN: %8.0f ", mst_len );
    printf( "MST_SEC: %f ", mst_time / timed_mst_runs );
    printf( "STNR_GAIN: %5.3f ", ((mst_len - stnr_len)*100.0) / mst_len );
    printf( "STNR_SEC: %f ", stnr_time / timed_stnr_runs );
    printf( "STNR_LEN: %8.0f ", stnr_len );
    printf( "NUM_ROUNDS: %2ld ", n_rounds );
    printf( "NUM_PHASES: %2ld ", n_phases );
    printf( "SEED: %2ld\n", seed );
  }

  /********************************** 
    free allocated memory 
  */
 
  free( pt );
  free( parent );
  stnr1_package_done();

  return  0;
}

/****************************************************************************/
/****************************************************************************/
