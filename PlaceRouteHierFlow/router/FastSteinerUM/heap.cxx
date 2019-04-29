/****************************************************************************/
/*
  Binary heap routines for use in Prim's algorithm, 
  with points are numbered from 0 to n-1
*/

#include <stdlib.h>
#include "heap.h"
#include "err.h"

namespace fastSteiner
{

Heap*   _heap = (Heap*)NULL;
long    _max_heap_size = 0;
long    _heap_size = 0;

/****************************************************************************/
/*
*/

void  allocate_heap( long n )
{
  if( _max_heap_size < n ) 
  {
    _heap = (Heap*)realloc( (void*)_heap, (size_t)(n+1)*sizeof(Heap) ); 
    if( ! _heap )
    {
      err_exit( "Cannot reallocate memory in allocate_heap!" );
    } 
    _max_heap_size = n;
  }
}
/****************************************************************************/
/*
*/

void  deallocate_heap()
{
  _max_heap_size = 0; 
  if( _heap )
  {
    free( (void*)_heap );
    _heap = (Heap*)NULL;
  }
}

/****************************************************************************/

void  heap_init( long  n )
{
  register long  p;

  allocate_heap( n );
  _heap_size = 0;
  for( p = 0;  p < n;  p++ )
  { 
    heap_idx( p ) = 0;
  }
 
} /* END heap_init() */

}

/****************************************************************************/
/****************************************************************************/

