#ifndef TAPREMOVAL_H_
#include <string>
#include <map>
#include <vector>
#include <string>
#include <climits>
#include <set>

#include "../PnRDB/datatype.h"

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// namespace for basic geometric point and rect classes
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
namespace geom {

using namespace std;

class Transform;

class Point {
  private:
    int _x, _y;
  public:
    Point(int x = INT_MAX, int y = INT_MAX) : _x(x), _y(y) {}
    Point(const Point& p) : _x(p._x), _y(p._y) {}
    Point(const PnRDB::point& p) : _x(p.x), _y(p.y) {}
    const int& x() const { return _x; }
    const int& y() const { return _y; }
    int& x() { return _x; }
    int& y() { return _y; }
    void scale(int t) { _x *= t; _y *= t; }
    void translate(int x, int y) { _x += x; _y += y; }
    void translate(int c) { _x += c; _y += c; }
    void translate(const Point& p) { _x += p.x(); _y += p.y(); }
    string toString() const { return to_string(_x) + "," + to_string(_y); }
    Point transform(const Transform& tr, const int width, const int height) const;
};

class Transform {
  private:
    Point _origin;
    unsigned _hflip : 1;
    unsigned _vflip : 1;

  public:
    Transform(const Point& o, const int hf, const int vf) :
      _origin(o), _hflip(hf == 0 ? 0 : 1), _vflip(vf == 0 ? 0 : 1) {}
    const Point& origin() const { return _origin; }
    bool hflip() const { return _hflip; }
    bool vflip() const { return _vflip; }
};

class Rect {
  private:
    Point _ll, _ur;

  public:
    const int& xmin() const { return _ll.x(); }
    const int& ymin() const { return _ll.y(); }
    const int& xmax() const { return _ur.x(); }
    const int& ymax() const { return _ur.y(); }
    int& xmin() { return _ll.x(); }
    int& ymin() { return _ll.y(); }
    int& xmax() { return _ur.x(); }
    int& ymax() { return _ur.y(); }
    const int xcenter() const { return (_ll.x() + _ur.x())/2; }
    const int ycenter() const { return (_ll.y() + _ur.y())/2; }

    void fix()
    {
      if (xmin() > xmax()) std::swap(xmin(), xmax());
      if (ymin() > ymax()) std::swap(ymin(), ymax());
    }
    Rect(const Point& ll, const Point& ur) : _ll(ll), _ur(ur) { fix(); }
    Rect(const int x1 = INT_MAX, const int y1 = INT_MAX, const int x2 = -INT_MAX, const int y2 = -INT_MAX) : _ll(x1, y1), _ur(x2, y2)
    {
      if (x1 != INT_MAX) fix();
    }
    Rect(const PnRDB::bbox& box) : _ll(box.LL), _ur(box.UR) {}
    void set(int x1 = INT_MAX, int y1 = INT_MAX, int x2 = -INT_MAX, int y2 = -INT_MAX)
    {
      _ll.x() = x1; _ll.y() = y1; _ur.x() = x2; _ur.y() = y2;
      if (x1 != INT_MAX) fix();
    }

    bool valid() const { return _ll.x() <= _ur.x() && _ll.y() <= _ur.y(); }

    bool intersect(const Rect& r)
    {
      int x1 = max(xmin(), r.xmin());
      int y1 = max(ymin(), r.ymin());
      int x2 = min(xmax(), r.xmax());
      int y2 = min(ymax(), r.ymax());
      xmin() = x1;
      ymin() = y1;
      xmax() = x2;
      ymax() = y2;
      return valid();
    }

    void merge(const Rect& r)
    {
      xmin() = min(xmin(), r.xmin());
      ymin() = min(ymin(), r.ymin());
      xmax() = max(xmax(), r.xmax());
      ymax() = max(ymax(), r.ymax());
    }

    void merge(const int x1, const int y1, const int x2, const int y2)
    {
      xmin() = min(xmin(), x1);
      ymin() = min(ymin(), y1);
      xmax() = max(xmax(), x2);
      ymax() = max(ymax(), y2);
    }

    void bloat(const int c) { _ll.translate(-c); _ur.translate(c); }
    Rect bloated(const int c) { return move(Rect(xmin() - c, ymin() - c, xmax() + c, ymax() + c)); }
    
    int width() const { return xmax() - xmin(); }
    int height() const { return ymax() - ymin(); }

    bool isVert() const { return width() <= height(); }
    bool isHor() const { return height() <= width(); }

    void translate(const int x, const int y) { _ll.translate(x, y); _ur.translate(x, y); }
    void translate(const int c) { _ll.translate(c); _ur.translate(c); }

    Rect translate(const Point& pt) const
    {
      auto r = Rect(_ll, _ur);
      r.translate(pt.x(), pt.y());
      return move(r);
    }

    Rect transform(const Transform& tr, const int width, const int height) const;

    long area() const { return ((long)width()) * height(); }
    string toString() const { return _ll.toString() + " -- " + _ur.toString(); }
};

typedef vector<Rect> Rects;

}
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// namespace for parsing and handling primitive data
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
namespace PrimitiveData {

using geom::Rect;
using geom::Rects;
using geom::Point;
using geom::Transform;

using namespace std;
using LayerRects = map<string, Rects>;

class Primitive
{
  private:
    string _name;
    Rect _bbox;
    Rects _taps, _actives;
    LayerRects _lr;
    bool _pmos;

  public:
    Primitive(const string& name, const Rect& r = Rect(), const bool pmos = false) : _name(name), _bbox(r), _pmos(pmos)
    {
      _taps.reserve(2);
      _actives.reserve(8);
    }

    const string& name() const { return _name; }
    string& name() { return _name; }

    void addTap(const Rect& t) { _taps.push_back(t); }
    void addTap(const int& x1, const int& y1, const int& x2, const int& y2) { _taps.emplace_back(x1, y1, x2, y2); }
    void addActive(const Rect& r) { _actives.push_back(r); }
    void addTaps(const Rects& t) { _taps.insert(_taps.end(), t.begin(), t.end()); }
    void addActives(const Rects& r) { _actives.insert(_actives.end(), r.begin(), r.end()); }

    void addLayerRects(const string& layer, const Rect& r) { _lr[layer].push_back(r); }

    const Rect& bbox() const { return _bbox; }
    long area() const { return _bbox.area(); }
    int width() const { return _bbox.width(); }
    int height() const { return _bbox.height(); }

    ~Primitive()
    {
      /*cout << _name << " : " << _lr.size() << ' ' << _taps.size() << ' ' << area() << endl;
      cout << "taps : " << endl;
      for (auto& t : _taps) {
        cout << t.toString() << endl;
      }
      cout << "rows : " << endl;
      for (auto& r : _actives) {
        cout << r.toString() << endl;
      }*/
    }

    const Rects& getTaps() const { return _taps; }
    const Rects& getActives() const { return _actives; }
    const bool isPMOS() const { return _pmos; }
};
using Primitives = map<string, vector<Primitive*> >;

struct PlInfo {
  string _primName;
  Transform _tr;
  PlInfo(const string& name, const geom::Point& ll, int hf, int vf) :
    _primName(name), _tr(ll, hf, vf) {}
};
typedef map<pair<string, unsigned>, PlInfo> PlMap;

class Instance
{
  private:
    const Primitive *_prim, *_primWoTap;
    string _name;
    Rects _taps, _actives;
    Rect _bbox;
    const int _woTapIndex;

  public:
    Instance(const Primitive* prim, const Primitive* primWoTap, const string& name, const Transform& tr, const int& wtIndex);
    ~Instance()
    {
      /*cout << _name << ' ' << _prim->name() << ' ' << _origin.toString() << endl;
      cout << "taps : " << endl;
      for (auto& t : _taps) {
        cout << t.toString() << endl;
      }
      cout << "rows : " << endl;
      for (auto& r : _actives) {
        cout << r.toString() << endl;
      }*/
    }

    long deltaArea() const { return (_prim != nullptr && _primWoTap != nullptr) ? (_prim->area() - _primWoTap->area()) : 0; }

    const string& name() const { return _name; }

    const Rects& getTaps() const { return _taps; }
    const Rects& getActives() const { return _actives; }
    const Rect& bbox() const { return _bbox; }
    const int index() const { return _woTapIndex; }

    bool isBlack() const { return _prim != nullptr && _primWoTap == nullptr; }

    const Primitive* primitive() const { return _prim; }

    void print() const;
};
typedef vector<Instance*> Instances;

}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// namespace for classes/routines to find the dominating set of tap nodes in a graph
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
namespace DomSetGraph {
using namespace std;

class Node;
class Edge;
typedef vector<Node*> Nodes;
typedef vector<const Node*> ConstNodes;
typedef map<const string, Node*> NodeMap;
typedef vector<Edge*> Edges;
typedef vector<const Edge*> ConstEdges;
typedef map<pair<const Node*, const Node*>, Edge*> EdgeMap;

enum class NodeType {
  Tap = 0,
  Active,
  MaxType
};

enum class NodeColor {
  Black = 0,
  Gray,
  White,
  MaxColor
};

class Node {
  private:
    string _name;
    NodeType _nt;
    ConstEdges _edges;
    unsigned _span;
    NodeColor _nc;
    long _deltaarea;
    bool _black;

  public:
    Node(const string& name, const NodeType nt = NodeType::Tap, const long& deltaarea = 0, const bool& isb = false) : _name(name), _nt(nt), _span(0), _nc(NodeColor::White), _deltaarea(deltaarea), _black(isb) {}
    const NodeType& nodeType() const { return _nt; }
    NodeType& nodeType() { return _nt; }

    const string type() const { return (_nt == NodeType::Tap) ? "T" : "A"; }
    const string& name() const { return _name; }

    string toString() const { return name() + " " + type(); }

    void addEdge(const Edge* e) { _edges.push_back(e); }
    const ConstEdges& edges() const { return _edges; }

    void setSpan(const unsigned n) { _span = n; }
    unsigned span() const { return _span; }

    void setColor(const NodeColor& nc) { _nc = nc; }
    const NodeColor& nodeColor() const { return _nc; }

    const long& deltaArea() const { return _deltaarea; }
    bool isBlack() const { return _black; }
};

struct NodeComp {
  bool operator() (const Node* const& n1, const Node* const& n2) const {
    if (n1 == nullptr) return false;
    if (n2 == nullptr) return true;
    if (n1->deltaArea() == n2->deltaArea()) return n1->name() < n2->name();
    return n1->deltaArea() < n2->deltaArea();
  }
};

typedef set<const Node*, NodeComp> NodeSet;

class Edge {
  private:
    const Node *_u, *_v;
    string _name;
  
  public:
    Edge(const Node* n1, const Node* n2, const string& name) : _u(n1), _v(n2), _name(name) {}
    const string& name() const { return _name; }
    const Node* u() const { return _u; }
    const Node* v() const { return _v; }
    string toString() const { return _u->name() + " " + _v->name() + " " + name(); }
};

class Graph {
  private:
    Nodes _nodes;
    NodeMap _nodeMap;
    Edges _edges;
    EdgeMap _edgeMap;

  public:
    Graph();
    ~Graph();

    void addNode(const string& name, const NodeType& nt, const long& da = 0, const bool isb = false);
    void addEdge(const string& u, const string& v, const string& name = "");

    const Edge* findEdge(const string& u, const string& v) const;

    void print() const;

    NodeSet dominatingSet() const;

    const Nodes& nodes() const { return _nodes; }
    const Edges& edges() const { return _edges; }

};

}

class TapRemoval {
  private:
    unsigned _dist;
    string _name;
    DomSetGraph::Graph *_graph;
    PrimitiveData::Instances _instances;
    PrimitiveData::Primitives _primitives, _primitivesWoTap;
    std::map<std::string, PrimitiveData::Instance*> _instMap;

    void buildGraph();
  public:
    TapRemoval(const PnRDB::hierNode& node, const unsigned dist);
    ~TapRemoval();
    bool valid() const { return !_primitives.empty() && !_primitivesWoTap.empty(); }
    //void createInstances(const PrimitiveData::PlMap& plmap);
    long deltaArea(std::map<std::string, int>* swappedIndices = nullptr) const;
    void rebuildInstances(const PrimitiveData::PlMap& plmap);
    bool containsPrimitive(const string& prim) const { return _primitives.find(prim) != _primitives.end(); }

    void plot(const string& pltfile, const map<string, int>* swappedIndices = nullptr) const;

};
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

#endif
