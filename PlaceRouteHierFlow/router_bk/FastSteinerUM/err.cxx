#include <stdio.h>
#include <stdlib.h>
#include "global.h"

namespace fastSteiner
{

/**************************************************************************/
/*
  print error message and continue
*/

void  err_msg(
const char* msg
)
{
  fprintf(stderr, "%s\n", msg);
}

/**************************************************************************/
/*
  print error message and  exit
*/

void  err_exit(
const char* msg
)
{
  fprintf(stderr, "%s\n", msg);
  exit(1);
}

/**************************************************************************/
/*
  check a sorted array
*/

int   is_sorted(void  *base,  size_t  nel,  size_t  width,   
                int (*compar)(const void *, const void *))
{
  size_t  i;

  for( i = 1;  i < nel;  i++ )
  {
    if( (*compar)( (void*)((size_t)base + i*width), 
                   (void*)((size_t)base + (i-1)*width) ) < 0 ) 
      return FALSE;
  }

  return  TRUE;
}

}
