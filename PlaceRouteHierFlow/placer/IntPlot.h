#ifndef INTPLOT_H_
#define INTPLOT_H_

#include <fstream>
#include <vector>
#include <map>
#include <set>
#include "design.h"
#include "SeqPair.h"
#include "ILP_solver.h"

using std::map;
using std::vector;
using std::string;
using std::pair;
using std::ofstream;
using std::set;
typedef map<string, PnRDB::bbox> CellBoxMap;

class MatPlotGen {
  private:
    unsigned _cnt;
    int _xmin, _ymin, _xmax, _ymax;
    set<string> _cells;
    string _costComp;
    ofstream _ofs;
  public:
    MatPlotGen(const string& _name);
    ~MatPlotGen();
    void addCostComp(const string& str) { if (_costComp.empty()) _costComp = str; }
    void addCells(const design& des);
    void addRow(const design& des, const SeqPair& curr_sp, const ILP_solver& ilp, const string& costStr);

};


#endif
