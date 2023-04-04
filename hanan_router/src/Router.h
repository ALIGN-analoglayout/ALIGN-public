#ifndef ROUTER_H_
#define ROUTER_H_
#include <set>
#include <map>
#include <queue>
#include <bitset>
#include <limits>
#include <memory>

#include "Util.h"
#include "Geom.h"
#include "Layer.h"

#define COST_MAX 10000

namespace Router {

typedef double CostType;
const auto CostTypeMax = std::numeric_limits<CostType>::max();
class Node;

class Via {
  private:
    int _l, _u, _c;
    Geom::Point _center;
    Geom::Rect _lb, _ub, _cut, _bbox;
    Geom::Rects _cuts;
  public:
    Via(const int l, const int u, const int c, const Geom::Point& ctr = Geom::Point(0, 0)) : _l{l}, _u{u}, _c{c}, _center{ctr}, _lb{}, _ub{}, _cut{}, _bbox{} {}
    Via(const Via& via, const Geom::Point& p = Geom::Point(0, 0));
    const Geom::Rect& bbox() const { return _bbox; }
    void setLB(const Geom::Rect& r) { _lb = r; _bbox.merge(_lb); }
    void setUB(const Geom::Rect& r) { _ub = r; _bbox.merge(_ub); }
    const Geom::Rects& cuts() const { return _cuts; }
    const Geom::Rect& upad() const { return _ub; }
    const Geom::Rect& lpad() const { return _lb; }
    const int u() const { return _u; }
    const int l() const { return _l; }
    void addCuts(const Geom::Point& o, const int wx, const int wy, const int nrow = 1, const int ncol = 1, const int sx = 0, const int sy = 0);
    Via translate(const Geom::Point& p) const;
    Via transform(const Geom::Transform& tr) const;
    std::string str() const;
    void addShapes(Geom::LayerRects& lr) const;
    Geom::LayerRects getShapes() const
    {
      Geom::LayerRects lr;
      addShapes(lr);
      return lr;
    }
};
typedef std::vector<std::shared_ptr<Via>> Vias;

class CostFn {
  private:
    int _topRoutingLayer;
    std::vector<CostType> _layerHCost, _layerVCost;
    std::vector<CostType> _savedLayerHCost, _savedLayerVCost;
    std::vector<std::vector<CostType>> _layerPairCost;
    std::set<int> _preflayers;
  public:
    CostType deltaCost(const Node& n1, const Node& n2) const;
    CostFn(const DRC::LayerInfo& lf);
    bool isVert(const int l) const { return _layerVCost[l] <= _layerHCost[l]; }
    bool isHor(const int l) const { return _layerHCost[l] <= _layerVCost[l]; }
    int topRoutingLayer() const { return _topRoutingLayer; }

    CostType hcost(int i) const { return _layerHCost[i]; }
    CostType vcost(int i) const { return _layerVCost[i]; }
    CostFn(const int numLayers = 0, const int minHLayer = 1, const int minVLayer = 0): _topRoutingLayer(numLayers - 1), _layerHCost(numLayers, COST_MAX), _layerVCost(numLayers, COST_MAX),
    _layerPairCost(numLayers, std::vector<CostType>(numLayers, COST_MAX))
    {
      for (int i = minHLayer; i < numLayers; i += 2) {
        _layerHCost[i] = 1;
      }
      for (int i = minVLayer; i < numLayers; i += 2) {
        _layerVCost[i] = 1;
      }
      for (int i = 0; i < numLayers; ++i) {
        if (i > 0) _layerPairCost[i][i-1] = 2;
        if (i < numLayers-1) _layerPairCost[i][i+1] = 2;
      }
      //for (int i = 0; i < numLayers; ++i) {
      //  COUT << "layer : " << i << " cost : " << _layerHCost[i] << ' ' << _layerVCost[i] << '\n';
      //}
    }
    void updatendr(const std::map<int, DRC::Direction>& ndrdir, const std::set<int>& preflayers);
    void resetdirs() {
      if (!_savedLayerHCost.empty()) _layerHCost = _savedLayerHCost;
      if (!_savedLayerVCost.empty()) _layerVCost = _savedLayerVCost;
      _preflayers.clear();
    }
};

class Router;

enum Direction
{
  DOWN = 0, UP, EAST, WEST, NORTH, SOUTH, MAXDIR
};

class Node {
#if DEBUG
  public:
    static size_t _nodectr;
#endif
  private:
    friend class Router;
    int _x, _y, _z;
    int _hwx, _hwy;
    CostType _fcost, _tcost;
    Node const* _parent;
    const Via *_upVia, *_dnVia;
    std::bitset<MAXDIR> _expanddir;
    Node(const int x = 0, const int y = 0, const int z = -1,
        const CostType fcost = -1, const CostType tcost = -1, Node const* parent = nullptr)
      : _x(x), _y(y), _z(z), _hwx{0}, _hwy{0}, _fcost(fcost), _tcost(tcost),
      _parent(parent), _upVia(nullptr), _dnVia(nullptr)
      {
        _expanddir.reset();
#if DEBUG
        ++_nodectr;
#endif
      }

    ~Node()
    {
      delete _upVia;
      delete _dnVia;
#if DEBUG
      --_nodectr;
#endif
    }
  public:
    bool closed() const { return _expanddir.none(); }
    int x() const { return _x; }
    int y() const { return _y; }
    int z() const { return _z; }
    Node const* parent() const { return _parent; }
    void sethwx(const int hwx) { _hwx = hwx; }
    void sethwy(const int hwy) { _hwy = hwy; }
    int hwx() const { return _hwx; }
    int hwy() const { return _hwy; }

    bool viadown()     const { return _expanddir.test(DOWN); }
    bool viaup()       const { return _expanddir.test(UP); }
    bool expandeast()  const { return _expanddir.test(EAST); }
    bool expandwest()  const { return _expanddir.test(WEST); }
    bool expandnorth() const { return _expanddir.test(NORTH); }
    bool expandsouth() const { return _expanddir.test(SOUTH); }

    void expand(const int dir, const bool val) { if (dir < MAXDIR) _expanddir.set(dir, val); }
    void setexpand() { _expanddir.set(); }
    void resetexpand() { _expanddir.reset(); }

    const Via* upVia() const { return _upVia; }
    const Via* dnVia() const { return _dnVia; }
    void upVia(const Via* v) { _upVia = v; }
    void dnVia(const Via* v) { _dnVia = v; }

    CostType fcost() const { return _fcost; }
    CostType tcost() const { return _tcost; }
    CostType cost()  const { return _fcost + _tcost;  }
    void setFCost(CostType fcost) { _fcost = fcost; }
    void setTCost(CostType tcost) { _tcost = tcost; }
    void setParent(const Node* n) { _parent = n; }
    void print(const std::string& s) const
    {
      COUT << s << "(" << _x << ',' << _y << ',' << _z << ") cost : (" << _fcost << ',' << _tcost <<  ',' << cost() << ") ";
      if (_expanddir.test(NORTH)) COUT << " N";
      if (_expanddir.test(SOUTH)) COUT << " S";
      if (_expanddir.test(EAST))  COUT << " E";
      if (_expanddir.test(WEST))  COUT << " W";
      if (_expanddir.test(UP))    COUT << " VU";
      if (_expanddir.test(DOWN))  COUT << " VD";
      COUT << '\n';
    }
};
typedef std::vector<Node*> NodePtrVec;
typedef std::vector<const Node*> NodeCPtrVec;
typedef std::vector<Node> NodeVec;
struct NodeComp {
  bool operator () (const Node* n1, const Node* n2) const
  {
    if (n1->x() == n2->x()) {
      if (n1->y() == n2->y()) {
        return n1->z() < n2->z();
      }
      return n1->y() < n2->y();
    }
    return n1->x() < n2->x();
  }
};
struct NodeCostComp {
  bool operator() (const Node* n1, const Node* n2) const
  {
    if (n1 != nullptr && n2 != nullptr) {
      if (n1->cost() == n2->cost()) {
        if (n1->fcost() == n2->fcost()) {
          return NodeComp()(n1, n2);
        }
        return n1->fcost() > n2->fcost();
      }
      return n1->cost() < n2->cost();
    }
    if (n1 == nullptr) return true;
    return false;
  }
};

typedef std::pair<int, int> IntPair;
struct IntPairComp {
  bool operator() (const IntPair& p1, const IntPair& p2) const
  {
    if (p1.first == p2.first) return p1.second < p2.second;
    return p1.first < p2.first;
  }
};
typedef std::set<IntPair, IntPairComp> IntRangeSet;
typedef std::set<Node*, NodeComp> NodeSet;
typedef std::multiset<const Node*, NodeCostComp> PriorityQueue;
typedef std::vector<std::map<IntPair, Node*, IntPairComp>> NodeMap;
class Router {
  private:
    PriorityQueue _pq;
    NodeSet _sources, _targets;
    NodeMap _nodes;
#if DEBUG
    std::set<Node*> _nodeset;
#endif
    Geom::LayerRects _obstacles, _tobstacles;
    CostFn _cf;
    std::vector<std::map<int, IntRangeSet>> _hanangridh, _hanangridv;
    Geom::Rect _bbox;
    const Node *_sol;
    std::vector<int> _widthx, _ndrwidthx, _spacex, _ndrspacex;
    std::vector<int> _widthy, _ndrwidthy, _spacey, _ndrspacey;
    int _minLayer, _maxLayer, _maxRoutingLayer;
    Vias _vias;
    std::vector<Vias> _upVias, _dnVias;
    std::string _name;
    size_t _expansions{0};
    const size_t _maxExpansions{10000};
    std::vector<int> _aboveViaLayer, _belowViaLayer;
    const DRC::LayerInfo& _lf;
    std::map<const Node*, int> _endextnxmin, _endextnymin, _endextnxmax, _endextnymax;
    std::map<int, std::set<Geom::Rect>> _sourceshapes, _targetshapes;
    std::string _modname, _netname;
    int _uu;
    int _precision{5};
    Geom::LayerTree _ltree;
    std::set<int> _preflayers;
    bool _usepinwidth{false}, _debugplot{false};

    Node* createNode(const int x = 0, const int y = 0, const int z = 0,
        const Node* parent = nullptr, const int fcost = -1, const int tcost = -1);

    void evalFCost(Node* n)
    {
      CostType fcost{0};
      if (n->parent()) {
        fcost = _cf.deltaCost(*n, *(n->parent())) + n->parent()->fcost();
      }
      n->setFCost(fcost);
    }

    void evalTCost(Node* n)
    {
      CostType tcost = CostTypeMax;
      for (auto& t : _targets) {
        tcost = std::min(tcost, _cf.deltaCost(*n, *t));
      }
      n->setTCost(tcost);
    }

    void evalCost(Node* n) { evalFCost(n); evalTCost(n); }

    void insertToPQ(const Node* n);

    void invertRange(IntRangeSet& s, const bool vert);
    void insertRange(IntRangeSet& s, const IntPair& r);
    void expandNode(const Node* n);
    void generateHananGrid();
    void checkAndInsert(Node* newn, const Node* n);
    int snap(const Node* n, const bool vert, const bool up) const;
    void getTargetGrid(std::set<int>& s, const Node* n, const bool vert, const int snapc);
    void getAdjacentGrid(std::set<int>& s, const Node* n, const bool above, const bool up, const int snapc);
    void flushNodes()
    {
      _pq.clear();
      for (auto& l : _nodes) {
        for (auto& n : l) {
          delete n.second;
#if DEBUG
          _nodeset.erase(n.second);
#endif
          n.second = nullptr;
        }
        l.clear();
      }
      _nodes.clear();
      _nodes.resize(_maxLayer + 1);
      COUT << "flushing nodes\n";
#if DEBUG
      COUT << " remaining " << Node::_nodectr << ' ' << _nodeset.size() << "\n";
      for (auto& n : _nodeset) {
        n->print("rem node : ");
      }
#endif
      _expansions = 0;
      _bbox = Geom::Rect();
    }
    Geom::PointWidthSet findValidPoints(const Geom::Rect& r, const int z, const Direction dir) const;

    bool isTarget(const Node* n) const { return _targets.find(const_cast<Node*>(n)) != _targets.end(); }
    bool isSource(const Node* n) const { return _sources.find(const_cast<Node*>(n)) != _sources.end(); }
    void setexpand(Node* newn, const Node* parent) const;

    void constructVias(const std::map<int, DRC::ViaArray>* ndrvias = nullptr);
    int roundup(const int x) const
    {
      auto r = x % _precision;
      return (r == 0) ? x : (x + _precision - r);
    }

    
  public:
    Router(const DRC::LayerInfo& lf);
    ~Router()
    {
      flushNodes();
      _sources.clear();
      _targets.clear();
      _vias.clear();
    }
    void readDataFile(const std::string& ifile);
    const int maxRoutingLayer() const { return _maxRoutingLayer; }
    const int maxLayer() const { return _maxLayer; }
    const int minLayer() const { return _minLayer; }
    void setName(const std::string& n) { _name = n; }
    void setusepinwidth(const bool u) { _usepinwidth = u; }

    int widthx(const int z) const { return (_ndrwidthx[z] != INT_MAX ? _ndrwidthx[z] : _widthx[z]); }
    int widthy(const int z) const { return (_ndrwidthy[z] != INT_MAX ? _ndrwidthy[z] : _widthy[z]); }
    int spacex(const int z) const { return (_ndrspacex[z] != INT_MAX ? _ndrspacex[z] : _spacex[z]); }
    int spacey(const int z) const { return (_ndrspacey[z] != INT_MAX ? _ndrspacey[z] : _spacey[z]); }

    void clearSourceTargets() {
      _cf.resetdirs();
      _sources.clear();
      _targets.clear();
      _sourceshapes.clear();
      _targetshapes.clear();
      _endextnxmin.clear();
      _endextnymin.clear();
      _endextnxmax.clear();
      _endextnymax.clear();
      _sol = nullptr;
      flushNodes();
      _bbox = Geom::Rect();
      _preflayers.clear();
    }
    Geom::LayerRects findSol();
    void printSol() const;
    void plot() const;
    void writeSTO() const;
    void clearObstacles(bool temp = false)
    {
      if(temp) _tobstacles.clear();
      else _obstacles.clear();
      _ltree.clear();
    }
    void addObstacles(const Geom::LayerRects& lr, const bool temp = false);

    void addSourceTargetShapes(const Geom::Rect& r, const int z, const bool src);
    void addSourceShapes(const Geom::Rect& r, const int z) { addSourceTargetShapes(r, z, true); }
    void addTargetShapes(const Geom::Rect& r, const int z) { addSourceTargetShapes(r, z, false); }
    void addSourceTarget(const Geom::Rect& r, const int z, const bool src);
    void addSource(const Geom::Rect& r, const int z) { addSourceTarget(r, z, true); }
    void addTarget(const Geom::Rect& r, const int z) { addSourceTarget(r, z, false); }
    const Via* isViaValid(const Node* n, const bool up) const;
    void updatendr(const bool usendr, const std::map<int, int>& ndrwidths,
        const std::map<int, int>& ndrspaces, const std::map<int, DRC::Direction>& ndrdirs,
        const std::set<int>& preflayers, const std::map<int, DRC::ViaArray>& ndrvias, const bool isVirtual);
    void setModName(const std::string& n) { _modname = n; }
    void setNetName(const std::string& n) { _netname = n; }
    void setuu(const int uu) { _uu = uu; }
    void allowDetour() { _bbox.expand(std::max(_bbox.width(), _bbox.height()) * 10); }
    void writeLEF(const Geom::LayerRects* sol = nullptr) const;
    void setEnableDebug(const bool b) { _debugplot = b; }
    bool debug() const { return _debugplot; }
};

}
#endif
