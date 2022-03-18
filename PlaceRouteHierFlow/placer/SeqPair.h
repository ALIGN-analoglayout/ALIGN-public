#ifndef SEQPAIR_h_
#define SEQPAIR_h_

#include <stdlib.h> /* srand, rand */

#include <algorithm>
#include <chrono>
#include <functional>
#include <iostream>
#include <memory>
#include <random>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "../PnRDB/readfile.h"
#include "Pdatatype.h"
#include "design.h"

using std::cerr;
using std::cout;
using std::endl;
using std::make_pair;
using std::pair;
using std::set;
using std::string;
using std::swap;
using std::vector;

class OrderedEnumerator {
  private:
  vector<vector<int>> _sequences;
  unsigned _cnt;
  bool TopoSortUtil(vector<int>& res, map<int, bool>& visited);
  vector<int> _seq;
  map<int, vector<int>> _adj;
  map<int, int> _indegree;
  bool _valid;
  const int _maxSeq;

  public:
  OrderedEnumerator(const vector<int>& seq, const vector<pair<pair<int, int>, placerDB::Smark>>& constraints, const int _maxSeq, const bool pos = true);
  void NextPermutation(vector<int>& seq, const int i) { seq = _sequences[i % _sequences.size()]; }
  void print();
  bool valid() const { return _valid; }
  size_t NumSequences() const { return _sequences.size(); }
};

class SeqPairEnumerator {
  private:
  vector<int> _posPair, _negPair, _selected;
  vector<int> _maxSelected;
  std::pair<size_t, size_t> _enumIndex;  // first : pos, second : neg
  int _maxSize;
  unsigned _exhausted : 1;
  unsigned _valid : 1;
  size_t _maxEnum;
  // size_t _hflip, _vflip;
  // size_t _maxFlip;
  OrderedEnumerator _posEnumerator, _negEnumerator;

  public:
  SeqPairEnumerator(const vector<int>& pair, design& casenl, const size_t maxIter);
  void Permute();
  const vector<int>& PosPair() const { return _posPair; }
  const vector<int>& NegPair() const { return _negPair; }
  const vector<int>& Selected() const { return _selected; }
  const bool EnumExhausted() const { return _exhausted; }
  const bool IncrementSelected();
  // bool EnumFlip();
  // vector<int> GetFlip(const bool hor) const;
  bool valid() const { return _valid ? true : false; }
};

class SeqPair {
  public:
  friend class ILP_solver;
  friend class ExtremeBlocksOfNet;
  friend class Placer;
  vector<int> posPair;
  vector<int> negPair;
  vector<placerDB::Omark> orient;
  vector<placerDB::Smark> symAxis;
  vector<int> selected;
  std::shared_ptr<SeqPairEnumerator> _seqPairEnum;
  vector<int> FindShortSeq(design& caseNL, vector<int>& seq, int idx);
  int GetVertexIndexinSeq(vector<int>& seq, int v);
  bool MoveAsymmetricBlockUnit(design& caseNL, vector<int>& seq, int anode);
  vector<int> GetVerticesIndexinSeq(vector<int>& seq, vector<int>& L);
  vector<int> SwapTwoListinSeq(vector<int>& Alist, vector<int>& Blist, vector<int>& seq);
  void InsertNewSBlock(design& originNL, int originIdx);

  public:
  SeqPair();
  SeqPair(int blockSize);
  SeqPair(string pos, string neg);
  SeqPair(const SeqPair& sp);
  SeqPair(design& caseNL, const size_t maxIter = 0);
  SeqPair& operator=(const SeqPair& sp);
  static size_t Factorial(const size_t& t);
  bool Enumerate() const { return _seqPairEnum ? true : false; }
  const bool EnumExhausted() const { return _seqPairEnum ? _seqPairEnum->EnumExhausted() : false; }
  void PrintSeqPair();
  void PrintVec(const string& tag, const vector<int>& vec);
  void SameSelected(design& caseNL);
  placerDB::Smark GetSymmBlockAxis(int SBidx);
  bool MoveAsymmetricBlockposPair(design& caseNL);
  bool MoveAsymmetricBlocknegPair(design& caseNL);
  bool MoveAsymmetricBlockdoublePair(design& caseNL);
  bool SwapTwoBlocksofSameGroup(design& caseNL);
  bool SwapMultiBlocksofSameGroup(design& caseNL);
  bool SwapTwoSymmetryGroup(design& caseNL);
  bool PerturbationNew(design& caseNL);
  bool CheckAlign(design& caseNL);
  bool CheckSymm(design& caseNL);
  void TestSwap();
  int GetBlockSelected(int blockNo);
  bool ChangeSelectedBlock(design& caseNL);
  bool KeepOrdering(design& caseNL);
  //bool ValidateSelect(design& caseNL);
  void CompactSeq();

  std::string getLexIndex(design& des) const;
  void cacheSeq(design& des) const { des.cacheSeq(posPair, negPair, selected); }
  bool isSeqInCache(const design& des) const { return des.isSeqInCache(posPair, negPair, selected); }

  // vector<int> GetFlip(const bool hor) const;
  bool operator==(const SeqPair& s1) const { return (posPair == s1.posPair) && (negPair == s1.negPair) && (selected == s1.selected); }
};

#endif
