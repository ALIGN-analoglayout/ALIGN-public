#include "toplevel.h"
#include <iostream>

int main(int argc, char** argv ){
  std::vector<std::string> args;
  for (unsigned int i=0; i<=argc; ++argc) {
    args.push_back( argv[i]);
  }
  std::cout << "Arguments set" << std::endl;
  return toplevel( args);
}
