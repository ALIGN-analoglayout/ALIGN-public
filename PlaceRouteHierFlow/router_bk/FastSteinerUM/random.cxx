/******************************************************************************
random.c -- random number generator; based on Knuth's Stanford GraphBase code
******************************************************************************/

#include  "random.h"

namespace fastSteiner
{

#define mod_diff( x, y )  ( ((x)-(y)) & MAX_LONG )


static long  A[56] = {-1};
long*  rg_ptr = A;


/****************************************************************************/
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


/****************************************************************************/
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

}

/****************************************************************************/
