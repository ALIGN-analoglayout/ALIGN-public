#ifndef _ERR_H_
#define _ERR_H_

namespace fastSteiner
{

void  err_msg( const char* msg );

void  err_exit( const char* msg );

int   is_sorted(void  *base,  size_t  nel,  size_t  width,
                int (*compar)(const void *, const void *));

}

#endif
