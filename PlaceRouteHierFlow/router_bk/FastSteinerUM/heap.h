#ifndef  _HEAP_H_
#define  _HEAP_H_

#include "global.h"

namespace fastSteiner
{

struct  heap_info
{
  double  key;
  long    idx;
  long    elt;
};

typedef  struct heap_info  Heap;

extern Heap*   _heap;
extern long    _max_heap_size;
extern long    _heap_size;

#define  heap_key( p )     ( _heap[p].key )
#define  heap_idx( p )     ( _heap[p].idx )
#define  heap_elt( k )     ( _heap[k].elt )

#define  in_heap( p )    ( heap_idx(p) > 0 )
#define  never_seen( p ) ( heap_idx(p) == 0 ) 

void   allocate_heap( long n );
void   deallocate_heap();
void   heap_init( long  n );



/****************************************************************************/

inline void  heap_insert( 
  long     p, 
  double   key 
)
{
  register long  k;       /* hole in the heap     */   
  register long  j;       /* parent of the hole   */
  register long  q;       /* heap_elt(j)          */

  heap_key( p ) = key;

  if( _heap_size == 0 )
  {
    _heap_size = 1;
    heap_elt( 1 ) = p;
    heap_idx( p ) = 1;          
    return;
  }

  k = ++ _heap_size;
  j = k >> 1;            /* k/2 */

  while( (j > 0) && (heap_key(q=heap_elt(j)) > key) ) { 

    heap_elt( k ) = q;
    heap_idx( q ) = k;
    k = j;
    j = k>>1;    /* k/2 */

  }
 
  /* store p in the position of the hole */
  heap_elt( k ) = p;
  heap_idx( p ) = k;      

} /* END heap_insert() */


/****************************************************************************/

inline void  heap_decrease_key
( 
  long    p, 
  double  new_key 
)
{
  register long    k;       /* hole in the heap     */   
  register long    j;       /* parent of the hole   */
  register long    q;       /* heap_elt(j)          */

  heap_key( p ) = new_key;
  k = heap_idx( p ); 
  j = k >> 1;            /* k/2 */

  if( (j > 0) && (heap_key(q=heap_elt(j)) > new_key) ) { /* change is needed */
    do {

      heap_elt( k ) = q;
      heap_idx( q ) = k;
      k = j;
      j = k>>1;    /* k/2 */

    } while( (j > 0) && (heap_key(q=heap_elt(j)) > new_key) );

    /* store p in the position of the hole */
    heap_elt( k ) = p;
    heap_idx( p ) = k;      
  }

} /* END heap_decrease_key() */


/****************************************************************************/

inline long  heap_delete_min()
{
  long    min, last;  
  register long   k;         /* hole in the heap     */   
  register long   j;         /* child of the hole    */
  register double l_key;     /* key of last point    */

  if( _heap_size == 0 )            /* heap is empty */
    return( -1 );

  min  = heap_elt( 1 );
  last = heap_elt( _heap_size -- );
  l_key = heap_key( last );

  k = 1;  j = 2;
  while( j <= _heap_size ) {

    if( heap_key(heap_elt(j)) > heap_key(heap_elt(j+1)) ) 
      j++;

    if( heap_key(heap_elt(j)) >= l_key)  
      break;                     /* found a position to insert 'last' */

    /* else, sift hole down */ 
    heap_elt(k) = heap_elt(j);    /* Note that j <= _heap_size */
    heap_idx( heap_elt(k) ) = k;
    k = j;
    j = k << 1;
  }

  heap_elt( k ) = last;
  heap_idx( last ) = k;

  heap_idx( min ) = -1;   /* mark the point visited */
  return( min );

} /* END heap_delete_min() */


/****************************************************************************/

}

#endif /* _HEAP_H_ */
