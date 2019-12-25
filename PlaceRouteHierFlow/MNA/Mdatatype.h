#ifndef MDATATYPE_H_
#define MDATATYPE_H_

#include <vector>
#include <string>
#include <map>
#include <utility>

namespace MDB {

  enum Element {R,I,V,C,L,X,M};

  struct device;
  struct metal_point;

  struct device{
    Element device_type;
    int start_point_index;
    int end_point_index;
    double value;
  };

  struct metal_point{
    int x;
    int y;
    int metal_layer;
    mutable int index;
  };

  struct Compare_metal_point {
    bool operator() (const metal_point& lhs, const metal_point& rhs) const{
      if(lhs.x==rhs.x){
         if(lhs.y==rhs.y){
          return lhs.metal_layer<rhs.metal_layer;
         }else{
          return lhs.y<rhs.y;
         } 
        }else{
          return lhs.x<rhs.x;
        }
    }
  };

}

#endif
