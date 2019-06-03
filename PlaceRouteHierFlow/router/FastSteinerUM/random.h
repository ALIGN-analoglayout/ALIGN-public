#ifndef _RANDOM_H_
#define _RANDOM_H_

namespace fastSteiner
{

void init_rand( long seed );
long flip_cycle();

extern long*  rg_ptr;

#define MAX_LONG ( 0x7fffffffL )
#define next_rand() ( *rg_ptr >= 0 ? *rg_ptr-- : flip_cycle() )

/****************************************************************************/
/*
unif_rand(m) -- uniform integers in range 0..m-1, assuming 1<m<=2^31. To
avoid the bias towards small values of next_rand()%m, the value returned
by next_rand() is used only if it falls in {r+1,...,2^31-1}, where r =
(2^31-1)%m + 1. (NOTE: slightly different from Knuth's SGB version.)
*/

inline long unif_rand( long m )
{ 
  register long  x;
  register long  r = MAX_LONG % m;
  
  do {
    x = next_rand();
  } while( x <= r );
  
  return( x % m );

} /* END unif_rand() */

}

#endif /* _RANDOM_H_ */

