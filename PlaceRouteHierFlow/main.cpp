#include "toplevel.h"
#include <iostream>

int main(int argc, char** argv ){
  std::vector<std::string> args;
  for (unsigned int i=0; i<argc; ++i) {
    args.push_back( argv[i]);
  }
  return toplevel( args);
}
