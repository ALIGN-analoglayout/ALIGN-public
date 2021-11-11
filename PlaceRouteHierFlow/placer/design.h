#ifndef DESIGN_h_
#define DESIGN_h_

#include <stdlib.h>

#include <climits>
#include <fstream>
#include <iostream>
#include <queue>
#include <random>
#include <set>
#include <sstream>
#include <string>
#include <utility>  // pair, make_pair
#include <vector>

#include "../PnRDB/datatype.h"
#include "../PnRDB/readfile.h"
#include "Pdatatype.h"
using std::cerr;
using std::cout;
using std::endl;
using std::iostream;
using std::make_pair;
using std::ofstream;
using std::pair;
using std::string;
using std::vector;

class design {
  private:
  friend class ConstGraph;
  friend class SeqPair;
  friend class SeqPairEnumerator;
  friend class Aplace;
  friend class Placer;
  friend class ILP_solver;
  //    enum NType {Block, Terminal};
  //    struct Node {
  //      NType type; // 1: blockPin; 2. Terminal
  //      int iter; // 1: #blockPin; 2. #Terminal
  //      int iter2; // 1: #block
  //    };
  //    struct point {
  //      int x;
  //      int y;
  //    };
  //    struct bbox {
  //      vector<point> polygon;
  //    };
  struct block {
    string name = "";
    placerDB::bbox boundary;
    string type = "";
    int width = 0;
    int height = 0;
    int SBidx = -1;
    int counterpart = -1;
    struct pin {
      string name;
      string type;
      vector<placerDB::point> center;
      vector<placerDB::bbox> boundary;
      PnRDB::bbox bbox;
      int netIter = -1;
    };
    bool bigMacro = true;
    int mapIdx = -1;
    vector<pin> blockPins;
  };

  struct terminal {
    string name;
    int netIter = -1;
    placerDB::point center;  // added a function to update the center point for each terminal when SA is finished, and plot write call this function.
    int SBidx = -1;
    int counterpart = -1;
  };
  //    struct net {
  //      string name;
  //      vector<Node> connected;
  //    };
  struct SymmNet {
    placerDB::net net1, net2;
    int SBidx = -1;
    placerDB::Smark axis_dir = placerDB::V;
  };
  struct SymmPairBlock {
    vector<pair<int, int>> sympair;
    vector<pair<int, placerDB::Smark>> selfsym;
    placerDB::Smark axis_dir = placerDB::V;
  };
  struct PortPos {
    int tid;
    placerDB::Bmark pos;
  };
  // struct SymmBlock {
  //  vector< pair<int,int> > sympair;
  //  vector< pair<int,Smark> > selfsym;
  //  int dnode;
  //};
  static std::mt19937_64 _rng;
  bool hasAsymBlock;
  bool hasSymGroup;
  int noBlock4Move;
  int noAsymBlock4Move;
  int noSymGroup4FullMove;
  int noSymGroup4PartMove;
  std::vector<std::vector<block>> Blocks;
  std::vector<terminal> Terminals;
  std::vector<placerDB::net> Nets;
  std::vector<SymmNet> SNets;
  std::vector<placerDB::SymmBlock> SBlocks;
  std::vector<SymmPairBlock> SPBlocks;
  std::vector<PortPos> Port_Location;
  std::vector<PnRDB::Multi_LinearConst> ML_Constraints;
  std::vector<pair<pair<int, int>, placerDB::Smark>> Ordering_Constraints;
  std::vector<pair<pair<int, int>, placerDB::Smark>> Abut_Constraints;
  vector<set<int>> Same_Template_Constraints;
  double Aspect_Ratio_weight = 1000;
  int placement_id = -1;
  bool is_first_ILP = true;
  double Aspect_Ratio[2] = {0, 100};
  double placement_box[2] = {-1.0, -1.0};
  double maxBlockAreaSum = 0;
  double maxBlockHPWLSum = 0;
  string name = "";

  // added by ya

  struct Preplace {
    int blockid1;
    int blockid2;
    string conner;
    int distance;
    int horizon;  // 1 is h, 0 is v.
  };

  vector<Preplace> Preplace_blocks;

  struct Alignment {
    int blockid1;
    int blockid2;
    int distance;
    int horizon;  // 1 is h, 0 is v.
  };

  vector<Alignment> Alignment_blocks;

  struct AlignBlock {
    std::vector<int> blocks;
    int horizon;  // 1 is h, 0 is v.
    int line;     // 0 is left or bottom, 1 is center, 2 is right or top
  };
  vector<AlignBlock> Align_blocks;

  struct Abument {
    int blockid1;
    int blockid2;
    int distance;
    int horizon;  // 1 is h, 0 is v.
  };

  struct MatchBlock {
    int blockid1;
    int blockid2;
    // int distance;
    // int horizon; // 1 is h, 0 is v.
  };

  vector<Abument> Abument_blocks;
  vector<MatchBlock> Match_blocks;
  int bias_Hgraph;
  int bias_Vgraph;
  bool mixFlag;
  void readRandConstFile(string random_const_file);
  // above is added by yg

  // void readBlockFile(string blockfile);
  // void readNetFile(string netfile);
  // void readConstFile(string cfile);
  void constructSymmGroup();
  placerDB::point GetPlacedPosition(placerDB::point oldp, int width, int height, placerDB::Omark ort);  // Get location of any point of block when placed
  vector<pair<int, int>> checkSympairInSymmBlock(vector<placerDB::SymmBlock>& SBs, vector<pair<int, int>>& Tsympair);
  vector<pair<int, int>> checkSelfsymInSymmBlock(vector<placerDB::SymmBlock>& SBs, vector<pair<int, placerDB::Smark>>& Tselfsym);
  // pair<int,int> checkSympairInSymmBlock(vector< pair<int,int> >& Tsympair);
  // pair<int,int> checkSelfsymInSymmBlock(vector< pair<int,placerDB::Smark> >& Tselfsym);
  placerDB::point GetMultPolyCenterPoint(vector<placerDB::point>& pL);
  int MergeNewBlockstoSymmetryGroup(vector<pair<int, int>>& tmpsympair, vector<pair<int, placerDB::Smark>>& tmpselfsym, vector<placerDB::SymmBlock>& SBs,
                                    vector<SymmNet>& SNs, placerDB::Smark axis_dir);
  int GetSizeAsymBlock4Move(int mode);
  int GetSizeSymGroup4PartMove(int mode);
  int GetSizeSymGroup4FullMove(int mode);
  int GetSizeBlock4Move(int mode);
  std::map<std::vector<int>, size_t> _seqPairHash, _selHash;
  bool _useCache{false};
  std::set<std::tuple<size_t, size_t, size_t>> _seqPairCache;
  std::vector<size_t> _factorial;
  size_t getSeqIndex(const vector<int>& seq);
  size_t getSelIndex(const vector<int>& sel);
  std::uniform_int_distribution<int>* _rnd{nullptr};
  enum class CompactStyle { L, R, C };
  CompactStyle compact_style = CompactStyle::L;

  public:
  design();
  design(PnRDB::hierNode& node, const int seed = 0);
  design(string blockfile, string netfile);
  design(string blockfile, string netfile, string cfile);
  int rand();
  bool leftAlign() const { return compact_style == CompactStyle::L; }
  bool rightAlign() const { return compact_style == CompactStyle::R; }

  // added by yg, the first one is to read in additional const, the other one is to generate random constrains.
  design(string blockfile, string netfile, string cfile, string random_const_file);
  design(string blockfile, string netfile, string cfile, string random_const_file, int write_out_flag);

  design(const design& other);
  design(design& other, int mode);
  design& operator=(const design& other);

  // generate_random_const file by yg
  void Generate_random_const(string random_constrain_file);
  //

  int GetSizeofBlocks();
  int GetSizeofTerminals();
  int GetSizeofNets();
  int GetSizeofSBlocks();
  int GetBlockSymmGroup(int blockid) const;
  int GetBlockCounterpart(int blockid);
  void PrintBlocks();
  void PrintTerminals();
  void PrintNets();
  void PrintConstraints();
  void PrintSymmGroup();
  void PrintDesign();
  vector<int> GetBlockListfromSymmGroup(int sgid);
  vector<int> GetRealBlockListfromSymmGroup(int sgid);
  vector<int> GetRealBlockPlusAxisListfromSymmGroup(int sgid);
  string GetBlockName(int blockid);
  string GetBlockPinName(int blockid, int pinid, int sel);
  string GetTerminalName(int termid);
  int GetBlockPinNum(int blockid, int sel);
  int GetBlockWidth(int blockid, placerDB::Omark ort, int sel);               // Get width of block when it's placed
  int GetBlockHeight(int blockid, placerDB::Omark ort, int sel);              // Get height of block when it's placed
  placerDB::point GetBlockCenter(int blockid, placerDB::Omark ort, int sel);  // Get relative location of block center when it's placed at origin
  placerDB::point GetBlockAbsCenter(int blockid, placerDB::Omark ort, placerDB::point LL,
                                    int sel);  // Get absolute location of block center when it's placed at LL
  vector<placerDB::point> GetPlacedBlockPinRelPosition(int blockid, int pinid, placerDB::Omark ort,
                                                       int sel);  // Get pin position of block when it's placed at origin
  vector<placerDB::point> GetPlacedBlockPinAbsPosition(int blockid, int pinid, placerDB::Omark ort, placerDB::point LL,
                                                       int sel);                                 // Get pin position of block when it's placed at LL
  vector<placerDB::point> GetPlacedBlockRelBoundary(int blockid, placerDB::Omark ort, int sel);  // Get block boundary when it's placed at origin
  vector<placerDB::point> GetPlacedBlockAbsBoundary(int blockid, placerDB::Omark ort, placerDB::point LL,
                                                    int sel);  // Get block boundary when it's placed at LL
  vector<vector<placerDB::point>> GetPlacedBlockPinRelBoundary(int blockid, int pinid, placerDB::Omark ort,
                                                               int sel);  // Get block pin boundary when it's placed at origin
  vector<vector<placerDB::point>> GetPlacedBlockPinAbsBoundary(int blockid, int pinid, placerDB::Omark ort, placerDB::point LL,
                                                               int sel);  // Get block pin boundary when it's placed at LL
  placerDB::point GetTerminalCenter(int teridx);
  bool checkAsymmetricBlockExist();
  bool checkSymmetricBlockExist();
  inline bool designHasAsymBlock() { return hasAsymBlock; };
  inline bool designHasSymGroup() { return hasSymGroup; };
  inline int GetSymGroupSize() { return SBlocks.size(); }
  int CheckCommonSymmGroup(design& reducedNL, placerDB::SymmBlock& reducedSB);
  int GetMappedBlockIdx(int idx);
  int GetMappedSymmBlockIdx(int idx);
  void ResetBlockMapIdx();
  void ResetSymmBlockMapIdx();
  std::vector<placerDB::SymmBlock> SplitSymmBlock(design& reducedNL, int originIdx);
  std::set<int> GetUnmappedBlocks();
  int GetBlockMargin(int i, int j);
  int GetBlockSymmGroupDnode(int i);

  PnRDB::point GetPlacedPnRPosition(PnRDB::point oldp, int width, int height, placerDB::Omark ort);
  PnRDB::bbox GetPlacedBlockInterMetalRelBox(int blockid, placerDB::Omark ort, PnRDB::bbox& originBox, int sel);
  PnRDB::bbox GetPlacedBlockInterMetalAbsBox(int blockid, placerDB::Omark ort, PnRDB::bbox& originBox, placerDB::point LL, int sel);
  PnRDB::point GetPlacedBlockInterMetalAbsPoint(int blockid, placerDB::Omark ort, PnRDB::point& originP, placerDB::point LL, int sel);
  PnRDB::point GetPlacedBlockInterMetalRelPoint(int blockid, placerDB::Omark ort, PnRDB::point& originP, int sel);
  void checkselfsym(vector<pair<int, int>>& tmpsympair, vector<pair<int, placerDB::Smark>>& tmpselfsym, placerDB::Smark tsmark);

  double GetMaxBlockAreaSum();
  double GetMaxBlockHPWLSum();
  ~design();

  size_t getSeqIndex(const vector<int>& seq) const;
  size_t getSelIndex(const vector<int>& sel) const;
  void cacheSeq(const vector<int>& p, const vector<int>& n, const vector<int>& sel);
  bool isSeqInCache(const vector<int>& p, const vector<int>& n, const vector<int>& sel) const;
  size_t _infeasAspRatio{0}, _infeasILPFail{0}, _infeasPlBound{0}, _totalNumCostCalc{0};
  // std::ofstream _debugofs;
};

#endif
