#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define  TRUE  1
#define  FALSE 0
#define  X_MAX ((long)1000000)
#define  Y_MAX ((long)1000000)

/*************************************************************************
Random number generator based on Knuth's Stanford GraphBase code:
*************************************************************************/

#define MAX_LONG ( 0x7fffffffL )
#define next_rand() ( *rg_ptr >= 0 ? *rg_ptr-- : flip_cycle() )
#define mod_diff( x, y )  ( ((x)-(y)) & MAX_LONG )


static long  A[56] = {-1};
long*  rg_ptr = A;

/************************************************************************/
/* 
flip_cycle() -- run 55 steps of the basic substractive recurrence; see 
Knuth's SGB. Not supposed to be called directly by the user. 
*/

long flip_cycle()
{
  register long  *ii, *jj;

  for(ii= &A[1], jj= &A[32]; jj <= &A[55]; ii++, jj++)
    *ii = mod_diff( *ii, *jj );

  for(jj= &A[1]; ii <= &A[55]; ii++, jj++)
    *ii= mod_diff(*ii,*jj);

  rg_ptr = &A[54];

  return( A[55] );

} /* END flip_cycle() */


/************************************************************************/
/*
init_rand(seed) -- initialize random generator; see Knuth's SGB.
*/

void init_rand( long seed )
{
  register long  i;
  register long  prev = seed, next= 1;

  seed  = prev = mod_diff( prev, 0 );
  A[55] = prev;

  for(i=21; i; i=(i+21)%55) {

    A[i] = next;
    next = mod_diff( prev, next );

    if( seed & 1 )
      seed = 0x40000000 + (seed>>1);
    else 
      seed >>= 1;

    next = mod_diff( next, seed );
    prev = A[i];
  }

  (void) flip_cycle();
  (void) flip_cycle();
  (void) flip_cycle();
  (void) flip_cycle();
  (void) flip_cycle();

} /* END init_rand */


/************************************************************************/
/*
unif_rand(m) -- uniform integers in range 0..m-1, assuming 1<m<=2^31. To
avoid the bias towards small values of next_rand()%m, the value returned
by next_rand() is used only if it falls in {r+1,...,2^31-1}, where r =
(2^31-1)%m + 1. (NOTE: slightly different from Knuth's SGB version.)
*/
  
long unif_rand( long m )
{
  register long  x;
  register long  r = MAX_LONG % m;

  do {
    x = next_rand();
  } while( x <= r );

  return( x % m );

} /* END unif_rand() */


/*************************************************************************
*************************************************************************/

void  generate_instance( long  num_terms, long  seed )
{
  long  new_x, new_y, i;
  char  x_in[X_MAX];
  char  y_in[Y_MAX];
  extern void  init_rand( long );
  extern long  unif_rand( long );

  init_rand( seed );

  for( i = 0;  i < X_MAX;  i++ )
    x_in[i] = FALSE;
  for( i = 0;  i < Y_MAX;  i++ )
    y_in[i] = FALSE;

  for( i = 0;  i < num_terms;  i++ ) {
    while( x_in[(new_x=unif_rand(X_MAX))] );   
    x_in[new_x] = TRUE;

    while( y_in[(new_y=unif_rand(Y_MAX))] );
    y_in[new_y] = TRUE;

    printf( "%6ld %6ld\n", new_x, new_y );
  }
}

/*************************************************************************
*************************************************************************/

int  main(
  int  argc, 
  char**  argv )
{
  long  i;
  long  num_terms = 0;
  long  seed = 1;

  for( i = 1; i < argc; i++) 
  {
    if(!strncmp(argv[i], "-t", strlen("-t")))
    {
      num_terms =  atol(argv[++i]);
    }
    else if(!strncmp(argv[i], "-s", strlen("-s")))
    {
      seed =  atol(argv[++i]);
    }
  }

  if( num_terms <= 0 ) {
    fprintf( stderr, "Usage: %s [-terminals N] [-seed N]\n", argv[0] );
  }
  else if( (num_terms >= X_MAX) || (num_terms >= Y_MAX) ) {
    fprintf( stderr, 
    "Too many terminals -- recompile with increased X_MAX and Y_MAX\n" );
  }
  else {
    printf( "%10ld\n", num_terms );
    generate_instance( num_terms, seed );
  }

  return 0;
}

/*************************************************************************
*************************************************************************/
