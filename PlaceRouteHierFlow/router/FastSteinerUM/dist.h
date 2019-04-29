#ifndef _DIST_H_
#define _DIST_H_

#include "global.h"

namespace fastSteiner
{

extern Metric  metric;

/*********************************************************************/
/*
   Return the rectilinear or octilinear distance between two points
*/

inline double  dist(
  Point  p,
  Point  q
)
{
  double  dx, dy;

  dx = p.x - q.x;
  if( dx < 0 )  dx = -dx;
  dy = p.y - q.y;
  if( dy < 0 )  dy = -dy;

  if( metric == RECTILINEAR )
  {
    return  dx + dy;
  }
  else
  {
    if( dx > dy )
    {
      return  dx - dy + dy*SQRT_TWO;
    }
    else
    {
      return  dy - dx + dx*SQRT_TWO;
    }
  }

}

/*********************************************************************/
/*
   Return the Manhattan distance between two points
*/

inline double  l1_dist(
  Point*  p,
  Point*  q
)
{
  double  dx, dy;
    
  dx = (p->x) - (q->x);
  if( dx < 0 )  dx *= -1;
  dy = (p->y) - (q->y);
  if( dy < 0 )  dy *= -1;

  return  dx + dy; 
}

/*********************************************************************/
/*********************************************************************/

}

#endif
