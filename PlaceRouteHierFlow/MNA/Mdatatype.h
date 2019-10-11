#ifndef MDATATYPE_H_
#define MDATATYPE_H_

#include <vector>
#include <string>
#include <map>
#include <utility>

namespace MDB {

  enum Element {R,I,V,C,L,X,M};

  struct device;

  struct device{
    Element device_type;
    int start_point;
    int end_point;
    double value;
  };

}

#endif
