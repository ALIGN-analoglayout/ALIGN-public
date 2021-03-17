#ifndef PDATATYPE_H
#define PDATATYPE_H
#include <algorithm>
#include <map>
#include <vector>
using std::map;
using std::pair;
using std::vector;


using namespace std;

struct Ppoint_F;
struct Ppoint_I;
struct block;
struct net;

struct Ppoint_F{ //placement point, float
    float x;
    float y;
};


struct Ppoint_I{ //placement point, int
    int x;
    int y;
};

//added by donghao
struct Alignment {
  int blockid1;
  int blockid2;
  float distance;//normalize to 0 - 1
  int horizon; // 1 is h, 0 is v.
};

struct bin {
    Ppoint_F Cpoint; //center point
    Ppoint_F Dpoint; //demension point: width/hight
    Ppoint_F Eforce; //force in X/Y direction
    float density; //E density in the bin
    float Ephi; // Ephi in the bin
    Ppoint_I Index; //index in X/Y of Bins[i][j]
};

struct block {
    string blockname = "";
    Ppoint_F Cpoint; //center point
    Ppoint_F Dpoint; //demension point: width/hight
    Ppoint_F Eforce; //Eforce in X/Y direction
    Ppoint_F Netforce; //Netforce in X/Y direction
    Ppoint_F Symmetricforce;
    Ppoint_F Force; // Force = Eforce + Netforce
    Ppoint_F Net_block_force_P; //Netforce in X/Y direction: exp(xi/gammer)
    Ppoint_F Net_block_force_N; //Netforce in X/Y direction: exp(-xi/gammer)
    vector<int> connected_net;
    int index; //index in Blocks[i]
};

struct net {
    string netname = "";
    vector<int> connected_block; // a vector stored the connected block
    int index; //index in Nets[i]
    Ppoint_F PSumNetforce; //Netforce in X/Y direction lse: sum( exp(xi/gammer) )
    Ppoint_F NSumNetforce; //Netforce in X/Y direction lse: sum( exp(-xi/gammer) )
    Ppoint_F PSumNetforce_WA; //sum Netforce in X/Y direction wa: sum( xi*exp(xi/gammer) )
    Ppoint_F NSumNetforce_WA; //sum Netforce in X/Y direction wa: sum( xi*exp(-xi/gammer) )
};

#endif