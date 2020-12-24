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

  struct metal_point{
    int x;
    int y;
    int metal_layer;
    mutable int index;
    double power;
    metal_point& operator += (const metal_point& other) { x = other.x; y = other.y; metal_layer=other.metal_layer; power=other.power; return *this; }
  };

  struct device{
    Element device_type;
    int start_point_index;
    int end_point_index;
    double value;
    int metal_layer;
    MDB::metal_point start_point;
    MDB::metal_point end_point;
   // int metal_layer2;
  };

struct Compare_metal_point {
  bool operator() (const metal_point& lhs, const metal_point& rhs) const{
      if(lhs.x==rhs.x){
         if(lhs.y==rhs.y){
           if(lhs.power==rhs.power){
               return lhs.metal_layer<rhs.metal_layer;
             }else{
               return lhs.power<rhs.power;
             }
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
