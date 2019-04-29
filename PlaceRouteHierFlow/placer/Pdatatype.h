#ifndef PDATATYPE_H_
#define PDATATYPE_H_

#include <vector>
#include <string>
//#include <iostream>
#include <utility>
using std::vector;
using std::string;
using std::pair;

namespace placerDB {

enum NType {Block, Terminal};
enum Omark {N, S, W, E, FN, FS, FW, FE};
enum Smark {H, V};

struct point {
  int x;
  int y;
};

struct Node {
  NType type; // 1: blockPin; 2. Terminal
  int iter; // 1: #blockPin; 2. #Terminal
  int iter2; // 1: #block
};

struct net {
  string name;
  vector<Node> connected;
  string priority;
};

struct bbox {
  vector<point> polygon;
};

struct SymmBlock {
  vector< pair<int,int> > sympair;
  vector< pair<int,Smark> > selfsym;
  int dnode;
};

}
#endif
