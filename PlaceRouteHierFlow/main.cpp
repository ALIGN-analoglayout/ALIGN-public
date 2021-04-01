#include "toplevel.h"
#include <iostream>
#include <memory>

int main(int argc, char** argv ){
  std::vector<std::string> args;
  for (unsigned int i=0; i<argc; ++i) {
    args.push_back( argv[i]);
  }
  std::unique_ptr<PnRdatabase> DB_ptr = toplevel( args);
  return 0;
}
