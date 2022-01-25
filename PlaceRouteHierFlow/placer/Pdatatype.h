#ifndef PDATATYPE_H_
#define PDATATYPE_H_

#include <string>
#include <vector>
//#include <iostream>
#include <utility>
using std::pair;
using std::string;
using std::vector;

class Pdatatype {
  public:
  static double LAMBDA;
  static double GAMAR;
  static double BETA;
  static double SIGMA;
  static double PHI;
  static double PI;
  static double PII;
};
namespace placerDB {

enum NType { Block, Terminal };
enum Omark { N, S, W, E, FN, FS, FW, FE };
enum Smark { H, V };
enum Bmark { TL, TC, TR, RT, RC, RB, BR, BC, BL, LB, LC, LT };

struct point {
  int x = 0;
  int y = 0;
  point(int ix, int iy) : x(ix), y(iy) {}
  point() : x(0), y(0) {}
  point& operator+=(const point& other) {
    x += other.x;
    y += other.y;
    return *this;
  }
  point& operator=(const point& other) {
    x = other.x;
    y = other.y;
    return *this;
  }
};

struct Node {
  NType type;  // 1: blockPin; 2. Terminal
  int iter;    // 1: #blockPin; 2. #Terminal
  int iter2;   // 1: #block
  double alpha;
};

struct net {
  string name;
  vector<Node> connected;
  string priority;
  int weight;      // weight for reduced design, used in HPWL
  int margin = 0;  // margin for reduced design, used in constraint graph
  double upperBound;
  double lowerBound;
};

struct bbox {
  vector<point> polygon;
};

struct SymmBlock {
  vector<pair<int, int> > sympair;
  vector<pair<int, Smark> > selfsym;
  int dnode;
  int mapIdx = -1;
  int axis_coor;
  Smark axis_dir = placerDB::V;
};


}  // namespace placerDB
#endif
