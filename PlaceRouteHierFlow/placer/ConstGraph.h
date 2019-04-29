#ifndef CONSTGRAPH_h_
#define CONSTGRAPH_h_

#include <cmath>
#include <utility>
#include <vector>
#include <stack>
#include <climits>
#include <string>
#include <iostream>
#include <fstream>
#include <algorithm>
#include <stdlib.h>     /* srand, rand */
#include <time.h>       /* time */
#include "Pdatatype.h"
#include "design.h"
#include "SeqPair.h"
#include "../PnRDB/datatype.h"

using std::vector;
using std::string;
using std::cout;
using std::cin;
using std::cerr;
using std::stack;
using std::pair;
using std::make_pair;
using std::min;
//using namespace std;
//using namespace placerDB;

#define NINF -9999999


class ConstGraph
{
  private:
    struct Edge {
      int next;
      int weight;
      bool isBackward;
    };
    struct Vertex {
      //int blockIdx;
      int weight;
      int position;
      int backpost;
      bool isSource;
      bool isSink;
      bool isVirtual;
      vector<Edge> Edges;
    };
    int origNodeSize;
    int sourceNode;
    int sinkNode;
    vector<Vertex> HGraph;
    vector<Vertex> VGraph;

    bool AddEdgeforVertex(int current, int next, int weight, vector<Vertex> &graph);
    //bool CheckOppositeEdge(int current, int next, vector<Vertex> &graph);
    //bool CheckRelatedForwardEdge(int current, int next, vector<Vertex> &graph);
    bool CheckForwardPath(int current, int next, vector<Vertex>& graph);
    void topologicalSortUtil(int v, bool visited[], stack<int> &Stack, vector<Vertex> &graph, bool backward );
    void CalculateLongestPath(int s, vector<Vertex> &graph, bool backward);
    int GetX(int i);
    int GetY(int i);
    double CalculatePenalty(vector<Vertex> &graph);
    double CalculateWireLength(design& caseNL, SeqPair& caseSP);
    double CalculateArea();
    double CalculateRatio();
    bool CheckPositiveCycle(vector<Vertex> &graph);
    vector<int> GenerateSlack(vector<int>& x);
    void UpdateLslackElement(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector< pair<int,placerDB::Smark> >& selfsym, vector<int>& Lslack, vector<int>& xL, int j, placerDB::Smark axis);
    bool CheckIfLslackViolation(vector<int>& Lslack );
    bool CheckIfSingleL2Violation(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis);
    int CheckIfL2ViolationUnit(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, int j, placerDB::Smark axis);
    pair<int,int> CheckIfL2Violation(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis);
    int CalculateBminusY(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis);
    int CalculateBminusXminusY(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, int j, int k, placerDB::Smark axis);
    void UpdatexLwithL3(design& caseNL, SeqPair& caseSP, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis);
    void AlignReorganize(design& caseNL, vector< pair<int,int> >& sympair, placerDB::Smark axis, int i);
    void InitializexL(design& caseNL, vector< pair<int,int> >& sympair, vector<int>& xL, placerDB::Smark axis, int i);
    PnRDB::bbox ConvertBoundaryData(vector<placerDB::point> Bdata);
    PnRDB::point ConvertPointData(placerDB::point Pdata);
    //void UpdateWeightforVertex(int current, int weight);
  public:
    static double LAMBDA;
    static double GAMAR;
    static double BETA;
    static double SIGMA;
    ConstGraph();
    ConstGraph(design& caseNL, SeqPair& caseSP);
    ConstGraph(const ConstGraph &cg);
    ConstGraph& operator=(const ConstGraph &cg);
    void PrintConstGraph();
    void Test(design& caseNL, SeqPair& caseSP);
    bool ConstraintHorizontalDistance(int n1, int n2, int c1, int c2 );
    bool ConstraintVerticalDistance(int n1, int n2, int c1, int c2 );
    void Update_parameters(design& caseNL, SeqPair& caseSP);
    bool ConstraintVerticalOrder(int below, int above);
    bool ConstraintHorizontalOrder(int left, int right);
    bool ConstraintGraph(design& caseNL, SeqPair& caseSP);
    double CalculateCost(design& caseNL, SeqPair& caseSP);
    double CalculateMatchCost(design& caseNL, SeqPair& caseSP);
    void updateTerminalCenter(design& caseNL, SeqPair& caseSP);
    void WritePlacement(design& caseNL, SeqPair& caseSP, string outfile);
    void PlotPlacement(design& caseNL, SeqPair& caseSP, string outfile);
    void UpdateHierNode(design& caseNL, SeqPair& caseSP, PnRDB::hierNode& node);
    bool FastInitialScan();
    void AddLargePenalty();
};

#endif
