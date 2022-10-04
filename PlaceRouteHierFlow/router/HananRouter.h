#ifndef HANAN_ROUTER_H_
#define HANAN_ROUTER_H_

#include <string>
#include <map>
#include <vector>
#include <string>
#include <climits>
#include <set>
#include <cmath>
#include <chrono>
#include <iostream>
#include <bitset>
#include <memory>

#include "../PnRDB/datatype.h"

namespace Geom {


using namespace std;
//using json = nlohmann::json;

class Transform;

class Point {
  private:
    int _x, _y;
  public:
    Point(int x = INT_MAX, int y = INT_MAX) : _x(x), _y(y) {}
    Point(const Point& p) : _x(p._x), _y(p._y) {}
    bool valid() const { return (_x != INT_MAX && _y != INT_MAX); }
    const int& x() const { return _x; }
    const int& y() const { return _y; }
    int& x() { return _x; }
    int& y() { return _y; }
    void set(const int x, const int y) { _x = x; _y = y; }
    void scale(int t) { _x *= t; _y *= t; }
    void translate(int x, int y) { _x += x; _y += y; }
    void translate(int c) { _x += c; _y += c; }
    void translate(const Point& p) { _x += p.x(); _y += p.y(); }
    Point trans(const Point& p) const { return Point(_x + p.x(), _y + p.y()); }
    //const json toJSON() const { return json{{"x", _x}, {"y", _y}}; }
    const std::string str() const { return "(" + std::to_string(_x) + "," + std::to_string(_y) + ")"; }
    bool operator < (const Point& p) const
    {
      if (_x == p._x) return _y < p._y;
      return _x < p._x;
    }
    bool operator == (const Point& p) const
    {
      return _x == p._x && _y == p._y;
    }

};
typedef std::set<Geom::Point> PointSet;
typedef std::set<std::pair<Geom::Point, int>> PointWidthSet;


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
    const Point& ll() const { return _ll; }
    const Point& ur() const { return _ur; }
    const int xcenter() const { return (_ll.x() + _ur.x())/2; }
    const int ycenter() const { return (_ll.y() + _ur.y())/2; }

    void fix()
    {
      if (xmin() == INT_MAX || ymin() == INT_MAX) return;
      if (xmin() > xmax()) std::swap(xmin(), xmax());
      if (ymin() > ymax()) std::swap(ymin(), ymax());
    }
    Rect(const Point& ll, const Point& ur) : _ll(ll), _ur(ur) { fix(); }
    Rect(const int x1 = INT_MAX, const int y1 = INT_MAX, const int x2 = INT_MIN, const int y2 = INT_MIN) : _ll(x1, y1), _ur(x2, y2)
    {
      fix();
    }
    void set(int x1 = INT_MAX, int y1 = INT_MAX, int x2 = INT_MIN, int y2 = INT_MIN)
    {
      _ll.x() = x1; _ll.y() = y1; _ur.x() = x2; _ur.y() = y2;
      fix();
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
    void bloat(const int x, const int y) { _ll.translate(-x, -y); _ur.translate(x, y); }
    Rect bloatby(const int c) const { return Rect(xmin() - c, ymin() - c, xmax() + c, ymax() + c); }
    Rect bloatby(const int x, const int y) const { return Rect(xmin() - x, ymin() - y, xmax() + x, ymax() + y); }
    Rect bloatby(const int x1, const int y1, const int x2, const int y2) const
    {
      return Rect(xmin() - x1, ymin() - y1, xmax() + x2, ymax() + y2);
    }
    
    int width()  const { return xmax()  - xmin(); }
    int height() const { return ymax()  - ymin(); }
    int halfpm() const { return width() + height(); }

    bool isVert() const { return width() <= height(); }
    bool isHor() const { return height() <= width(); }

    void translate(const int x, const int y) { _ll.translate(x, y); _ur.translate(x, y); }
    void translate(const int c) { _ll.translate(c); _ur.translate(c); }

    Rect trans(const Point& pt) const
    {
      auto r = Rect(_ll, _ur);
      r.translate(pt.x(), pt.y());
      return r;
    }

    long area() const { return ((long)width()) * height(); }
    string str() const { return "[" + _ll.str() + "," + _ur.str() + "]"; }
    //const json toJSON() const { return json{{"LL", _ll.toJSON()}, {"UR", _ur.toJSON()}}; }

    bool overlaps (const Geom::Rect& r, const bool strict = false) const 
    {
      if (strict) {
        if (xmin() <= r.xmax() && xmax() >= r.xmin()
            && ymin() <= r.ymax() && ymax() >= r.ymin())
          return true;
      } else {
        if (xmin() < r.xmax() && xmax() > r.xmin()
            && ymin() < r.ymax() && ymax() > r.ymin())
          return true;
      }
      return false;
    }

    bool contains (const int x, const int y, bool strict = true) const
    {
      if (strict) {
        return x > xmin() && x < xmax() && y > ymin()  && y < ymax();
      }
      return x >= xmin() && x <= xmax() && y >= ymin() && y <= ymax();
    }

    bool contains (const Geom::Point& p, bool strict = true) const
    {
      if (strict) {
        return p.x() > xmin() && p.x() < xmax() && p.y() > ymin() && p.y() < ymax();
      }
      return p.x() >= xmin() && p.x() <= xmax() && p.y() >= ymin() && p.y() <= ymax();
    }

    bool contains (const Geom::Rect& r) const
    {
      return contains(r._ll, false) && contains(r._ur, false);
    }

    bool operator < (const Rect& r) const
    {
      if (_ur == r._ur) return _ll < r._ll;
      return _ur < r._ur;
    }
};
typedef vector<Rect> Rects;
typedef map<int, Rects> LayerRects;

class Transform {
  private:
    Point _o;
    int _sX, _sY; 

  public:
    Transform(const int x = 0, const int y = 0, const int sx = 1, const int sy = 1) :
      _o{x, y}, _sX{sx}, _sY{sy} {}
    const Point& origin() const { return _o; }
    const int x() const { return _o.x(); }
    const int y() const { return _o.y(); }
    int sX() const { return _sX; }
    int sY() const { return _sY; }
    std::string orient() const
    {
      if (_sX == 1 && _sY == 1) return "N";
      if (_sX == -1 && _sY == 1) return "FN";
      if (_sX == 1 && _sY == -1) return "FS";
      return "S";
    }
    void apply(Point& pt) const 
    {
      pt.x() = _o.x() + _sX * pt.x();
      pt.y() = _o.y() + _sY * pt.y();
    }
    Point transform(const Point& pt) const
    {
      return Point(_o.x() + _sX * pt.x(), _o.y() + _sY * pt.y());
    }
    void apply(Rect& r) const 
    {
      r.xmin() = _o.x() + _sX * r.xmin();
      r.ymin() = _o.y() + _sY * r.ymin();
      r.xmax() = _o.x() + _sX * r.xmax();
      r.ymax() = _o.y() + _sY * r.ymax();
      r.fix();
    }
    Rect transform(const Rect& r) const
    {
      return Rect(transform(r.ll()), transform(r.ur()));
    }
    //const json toJSON() const { return json{{"Origin", _o.toJSON()}, {"sX", _sX}, {"sY", _sY}}; }
    const std::string str() const { return ("origin : {" + _o.str() + "} sX : " + std::to_string(_sX) + " sY : " + std::to_string(_sY)); }
};

double Dist(const Geom::Rect& r1, const Geom::Rect& r2, const bool manh = true);
void MergeLayerRects(Geom::LayerRects& l1, const Geom::LayerRects& l2, Geom::Rect* b = nullptr);
}

namespace DRC {

using namespace std; 

enum class Direction {
  HORIZONTAL,
  VERTICAL,
  ORTHOGONAL
};

enum class LayerType {
  METAL,
  VIA
};

class Layer {
  private:
    const int _gdsNo;
    const std::string _name;
    const float _r[3]; // mean, -3\sigma, 3\sigma
    const LayerType _type;
    int _index;
  public:
    Layer(const int gdsNo, const std::string& name, const float mur, const float lr, const float ur, const LayerType type)
      : _gdsNo(gdsNo), _name(name), _r{mur, lr, ur}, _type{type}, _index{-1} {}
    int gdsNo() const { return _gdsNo; }
    const std::string& name() const { return _name; }
    float meanR() const { return _r[0]; }
    bool isMetal() const { return _type == LayerType::METAL; }
    bool isVia() const { return _type == LayerType::VIA; }
    void setIndex(const int i) { _index = i; }
    int index() const { return _index; }
    ~Layer()
    {
      //std::cout << "layer : " << _name << ' ' << _gdsNo << " {" << _r[0] << ',' << _r[1] << ',' << _r[2] << "}\n";
    }
};
typedef std::vector<Layer*> Layers;

class gdsDatatype {
  public:
    int _draw{0}, _pin{0}, _label{0}, _blockage{0};
};

class MetalLayer : public Layer {
  private:
    int _pitch, _width, _minL, _maxL;
    int _e2e, _offset;
    float _c[3], _cc[3];
    Direction _dir;
  public:
    MetalLayer(const int gdsNo, const std::string& name, const float mur, const float lr, const float ur)
      : Layer(gdsNo, name, mur, lr, ur, LayerType::METAL), _pitch(0), _width(0), _minL(0), _maxL(0), _e2e(0), _offset(0),
    _c{0,0,0}, _cc{0, 0, 0}, _dir(Direction::ORTHOGONAL) {}
    int pitch() const { return _pitch;}
    int width() const { return _width;}
    int space() const
    {
      return (_pitch > _width) ? (_pitch - _width) : _pitch;
    }
    void setPitch(const int p) {_pitch = p;}
    void setWidth(const int w) {_width = w;}
    void setMinL(const int l) {_minL = l;}
    void setMaxL(const int l) {_maxL = l;}
    void setE2E(const int e) {_e2e = e;}
    void setOffset(const int o) {_offset = o;}
    void setDirection(const int dir) { _dir = (dir == 0 ? Direction::HORIZONTAL : (dir == 1 ? Direction::VERTICAL : Direction::ORTHOGONAL)); }
    void setC(const float muc, const float lc, const float uc) { _c[0] = muc; _c[1] = lc; _c[2] = uc; }
    void setCC(const float muc, const float lc, const float uc) { _cc[0] = muc; _cc[1] = lc; _cc[2] = uc; }
    bool isHorizontal() const { return _dir == Direction::HORIZONTAL || _dir == Direction::ORTHOGONAL; }
    bool isVertical() const { return _dir == Direction::VERTICAL || _dir == Direction::ORTHOGONAL; }
    ~MetalLayer()
    {
      //std::cout << _pitch << ' ' << _width << ' ' << _minL << ' ' << _maxL << ' ' << _e2e << ' ' << _offset << ' ';
      //std::cout << (_dir == Direction::HORIZONTAL ? "hor" : "ver") << ' ';
    }
};
typedef std::vector<MetalLayer*> MetalLayers;

class ViaLayer : public Layer {
  private:
    struct SpaceWidth {
      std::pair<int, int> _space, _width; // 0 : x, 1 : y
      SpaceWidth() : _space{0, 0}, _width{0, 0} {}
    };
    SpaceWidth _sw;
    std::pair<const MetalLayer*, const MetalLayer*> _layerPair; // first : lower, second : upper
    int _coverl[2], _coveru[2]; // 0 : low, 1 : high
    struct ViaArray {
      SpaceWidth _sw;
      int _nx, _ny;
      ViaArray() : _sw{}, _nx{0}, _ny{0} {}
      ViaArray(const int  wx, const int wy, const int sx, const int sy, const int nx, const int ny)
      {
        _sw._space = std::make_pair(sx, sy);
        _sw._width = std::make_pair(wx, wy);
        _nx = nx;
        _ny = ny;
      }
    };
    std::vector<ViaArray> _va;
  public:
    ViaLayer(const int gdsNo, const std::string& name, const float mur, const float lr, const float ur)
      : Layer(gdsNo, name, mur, lr, ur, LayerType::VIA), _sw{}, _layerPair(nullptr, nullptr),
      _coverl{0, 0}, _coveru{0, 0} {}
    void setSpace(const int x, const int y) {_sw._space.first = x; _sw._space.second = y;}
    void setWidth(const int x, const int y) {_sw._width.first = x; _sw._width.second = y;}
    void setCoverL(const int x, const int y) {_coverl[0] = x; _coverl[1] = y;}
    void setCoverU(const int x, const int y) {_coveru[0] = x; _coveru[1] = y;}
    void setLayerPair(const MetalLayer* m1, const MetalLayer* m2) {_layerPair = std::make_pair(m1, m2); }
    void addViaArray(const int wx, const int wy, const int sx, const int sy, const int nx, const int ny)
    {
      _va.push_back(ViaArray(wx, wy, sx, sy, nx, ny));
    }
    ~ViaLayer()
    {
      //std::cout << _sw._space[0] << ' ' << _sw._space[1] << " -- " << _width[0] << ' ' << _width[1] << ' ';
      //std::cout << (_layerPair.first ? _layerPair.first->name() : " ") << ' ';
      //std::cout << (_layerPair.second ? _layerPair.second->name() : " ") << ' ';
      //std::cout << _coverl[0] << ' ' << _coverl[1] << " -- " << _coveru[0] << ' ' << _coveru[1] << ' ';
    }
    const std::vector<ViaArray>& viaArray() const { return _va; }
    const std::pair<const MetalLayer*, const MetalLayer*>& layers() const { return _layerPair; }
    int widthx() const { return _sw._width.first; }
    int widthy() const { return _sw._width.second; }
    int coverlx() const { return _coverl[0]; }
    int coverly() const { return _coverl[1]; }
    int coverux() const { return _coveru[0]; }
    int coveruy() const { return _coveru[1]; }
    void swapcover(bool up)
    {
      if (up) std::swap(_coveru[0], _coveru[1]); 
      else std::swap(_coverl[0], _coverl[1]); 
    }
    int spacex() const { return _sw._space.first; }
    int spacey() const { return _sw._space.second; }

};
typedef std::vector<ViaLayer*> ViaLayers;

class LayerInfo {
  private:
    MetalLayers _mlayers;
    ViaLayers _vlayers;
    Layers _layers;
    std::map<std::string, int> _layerIndex;
    std::map<const MetalLayer*, const ViaLayer*> _vldn, _vlup;
    std::map<std::string, MetalLayer*> _mlayerNameMap;
    MetalLayer *_sbottom, *_stop, *_cbottom, *_ctop, *_pbottom, *_ptop;
    int _topMetal;
    bool _populated;
  public:
    LayerInfo(const std::string& lj, const int uu);
    void print() const;
    ~LayerInfo();
    int getLayerIndex(const std::string& name) const
    {
      auto it = _layerIndex.find(name);
      return ((it != _layerIndex.end()) ? it->second : -1);
    }
    std::pair<int, int> getLayers(const ViaLayer* v) const
    {
      auto l = v->layers();
      if (l.first && l.second) return std::make_pair(l.first->index(), l.second->index());
      return std::make_pair(-1, -1);
    }
    const Layers& layers() const { return _layers; }
    int signalBottomLayer() const 
    {
      if (_sbottom) return _sbottom->index();
      for (int i = 0; i < static_cast<int>(_layers.size()); ++i) {
        if (_layers[i]->name() == "M1") return i;
      }
      return 0;
    }
    int signalTopLayer() const { return (_stop ? _stop->index() : _topMetal); }
    bool populated() const { return _populated; }
    bool isVertical(const int z) const
    {
      if (z < static_cast<int>(_layers.size()) && _layers[z]->isMetal()) {
        return static_cast<MetalLayer*>(_layers[z])->isVertical();
      }
      return true;
    }
    bool isHorizontal(const int z) const
    {
      if (z < static_cast<int>(_layers.size()) && _layers[z]->isMetal()) {
        return static_cast<MetalLayer*>(_layers[z])->isHorizontal();
      }
      return true;
    }
};

}


namespace HananRouter{
class Router;
class Via;
typedef std::vector<std::shared_ptr<Via>> Vias;
};

namespace Placement {

class Module;
class Netlist;
class Instance;
typedef std::vector<Instance*> Instances;
typedef std::map<std::string, Module*> Modules;

class Pin {
  private:
    std::string _name;
    Geom::LayerRects _shapes;
    Geom::Rect _bbox;
    int _real; // 1 : real, 0 : virtual
  public:
    Pin(const std::string& name = "", const int r = 1) : _name{name}, _bbox{}, _real{r} {}
    const std::string& name() const { return _name; }
    void addRect(const int layer, const Geom::Rect& r)
    {
      _shapes[layer].push_back(r);
      _bbox.merge(r);
    }
    void clearRects()
    {
      _bbox = Geom::Rect();
      _shapes.clear();
    }
    const Geom::LayerRects& shapes() const { return _shapes; }
    const Geom::Rect& bbox() const { return _bbox; }
    void copyRects(const Geom::LayerRects& lr)
    {
      Geom::MergeLayerRects(_shapes, lr, &_bbox);
    }
    int isReal() const { return _real; }
    int minLayer() const { return (_shapes.empty() ? -1 : _shapes.begin()->first); }
};
typedef std::map<std::string, Pin*> Pins;
typedef std::vector<const Pin*> PinCVec;
typedef std::vector<std::pair<const Pin*, const Pin*>> PinPairs;
class Net {
  private:
    std::string _name;
    std::set<const Pin*> _pins;
    std::vector<Pin*> _vpins;
    Geom::LayerRects _routeshapes;
    Geom::Rect _bbox;
    int _unroute : 1;
    //PinPairs reorderPins() const;
    double findMST(PinPairs& porder) const;
    PinPairs findSteiners();
  public:
    Net(const std::string& name) : _name{name}, _bbox{}, _unroute{1} {}
    ~Net()
    {
      for (auto& v : _vpins) delete v;
      _vpins.clear();
    }
    const std::set<const Pin*>& pins() const { return _pins; }
    const std::vector<Pin*>& vpins() const { return _vpins; }
    void addPin(const Pin* p) { _pins.insert(p); }
    void print() const;
    const std::string& name() const { return _name; }
    void route(HananRouter::Router& r, const Geom::LayerRects& l1, const Geom::LayerRects& l2, const Geom::LayerRects& l3, const bool update);
    const Geom::LayerRects& routeShapes() const { return _routeshapes; }
    const Geom::Rect& bbox() const { return _bbox; }
    const bool open() const { return _unroute ? true : false; }
    void update()
    {
      for (auto& p : _pins) {
        for (auto& l : p->shapes()) {
          for (auto& s : l.second) {
            _bbox.merge(Geom::Rect(s.xcenter(), s.ycenter(), s.xcenter(), s.ycenter()));
          }
        }
      }
    }
    int halfpm() const { return _bbox.halfpm(); }
};
typedef std::map<std::string, Net> Nets;
typedef std::vector<Net*> NetsVec;


class Instance {
  friend class Module;
  private:
    std::string _name, _modname;
    Geom::Transform _tr;
    const Module* _m;
    Pins _pins;
    Geom::LayerRects _routeshapes;
    HananRouter::Vias _vias;
    void build(const bool rebuild = false);
    Geom::Rect _bbox;
  public:
    Instance(const std::string& iname = "", const std::string& mname = "", const Geom::Transform& tr = Geom::Transform()) :
      _name(iname), _modname(mname), _tr(tr), _m(nullptr), _bbox{} {}
    ~Instance();
    const Module* module() const {return _m; }
    const std::string& name() const { return _name; }
    const std::string& moduleName() const { return _modname; }
    const Geom::Transform& transform() const { return _tr; }
    Geom::Rect transform(const Geom::Rect& r) const { return _tr.transform(r); }
    void setModule(const Module* m);
    void print(const std::string& prefix = "") const;
    const Geom::Rect& bbox() const { return _bbox; }
    const Pins& pins() const { return _pins; }
    const Geom::LayerRects& routeShapes() const { return _routeshapes; }
};


class Module {
  friend class Netlist;
  private:
    std::string _name;
    int _leaf : 1;
    int _routed : 1;
    Nets _nets;
    Pins _pins;
    Instances _instances;
    HananRouter::Vias _vias;
    std::map<const Net*, std::vector<std::pair<Instance*, std::string>>> _tmpnetpins;
    Geom::LayerRects _obstacles;
    Geom::Rect _bbox;
    const int _uu;

    void build();
  public:
    Module(const std::string& name, const int leaf, const int uu) : _name(name), _leaf(leaf), _routed{leaf}, _bbox{}, _uu{uu} {_instances.reserve(64);}
    ~Module();
    Instance* addInstance(const std::string& name, const std::string& mname, const Geom::Transform& tr)
    {
      _instances.emplace_back(new Instance(name, mname, tr)); 
      return _instances.back();
    }
    bool routed() const { return (_routed ? true : false); }
    const std::string& name() const { return _name; }
    const Instances& instances() const { return _instances; }
    Instances& instances() { return _instances; }
    const Geom::LayerRects& obstacles() const { return _obstacles; }
    bool isLeaf() const { return _leaf ? true : false; }
    const Nets& nets() const { return _nets; }
    const Pins& pins() const { return _pins; }

    void setBBox(const Geom::Rect& b) { _bbox = b; }
    void setRouted() { _routed = 1; }
    Pin* addPin(const std::string& name)
    {
      Pin* p{nullptr};
      auto it = _pins.find(name);
      if (_pins.find(name) == _pins.end()) {
        p = new Pin(name);
        _pins[name] = p;
      } else {
        p = it->second;
      }
      return p;
    }
    const Net& addNet(const std::string& name)
    {
      auto it = _nets.find(name);
      if (it == _nets.end()) {
        it = _nets.emplace(name, name).first;
      }
      return it->second;
    }
    Net* net(const std::string& name)
    {
      auto it = _nets.find(name);
      if (it != _nets.end()) return &(it->second);
      return nullptr;
    }
    void addTmpPin(const Net* n, Instance* inst, const std::string& pname)
    {
      if(n) _tmpnetpins[n].push_back(std::make_pair(inst, pname));
    }
    Pin* getPin(const std::string& pn)
    {
      auto it = _pins.find(pn);
      return ((it != _pins.end()) ? it->second : nullptr);
    }
    void addObstacle(const int layer, const Geom::Rect& r)
    {
      _obstacles[layer].push_back(r);
    }
    void updateNets()
    {
      for (auto& n : _nets) {
        n.second.update();
      }
    }

    void print() const;
    void route(HananRouter::Router& r);
    void plot() const;

    const Geom::Rect& bbox() const { return _bbox; }
    void checkShort() const;

    void writeDEF(const std::string& nstr = "", const std::string& netname = "") const;
    void writeLEF() const;

};


class Netlist {
  private:
    const int _uu;
    int _valid;
    Modules _modules;
    void build();
    void loadLEF(const std::string& leffile, const DRC::LayerInfo& lf);

  public:
    Netlist(const std::string& plfile, const::std::string& leffile, const DRC::LayerInfo& lf, const int uu);
    ~Netlist();
    void print() const;
    void route(HananRouter::Router& r)
    {
      if (!_valid) return;
      for (auto& m : _modules) m.second->route(r);
    }
    void plot() const
    {
      for (auto& m : _modules) m.second->plot();
    }
    void checkShort() const
    {
      if (!_valid) return;
      for (auto& m : _modules) m.second->checkShort();
    }
    void writeDEF() const
    {
      if (!_valid) return;
      for (auto& m : _modules) if (!m.second->isLeaf()) m.second->writeDEF();
    }
};


}

class TimeMeasure {
  private:
    const std::string _name;
    std::chrono::nanoseconds* _rt;
    std::chrono::high_resolution_clock::time_point _begin;
  public:
    TimeMeasure(const std::string& name, std::chrono::nanoseconds* rt = nullptr) : _name(name), _rt(rt)
    {
      _begin = std::chrono::high_resolution_clock::now();
    }
    ~TimeMeasure()
    {
      auto difft = std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::high_resolution_clock::now() - _begin);
      if (_rt) {
        (*_rt) += difft;
      } else {
        std::cout << _name << " runtime : " << difft.count()/1.e9 << "(s)\n";
      }
    }
};

extern const std::vector<std::string> LAYER_COLORS;

std::string parseArgs(const int argc, char* const argv[], const std::string& arg, std::string str = "");
bool checkArg(const int argc, char* const argv[], const std::string& arg);

extern std::vector<std::string> LAYER_NAMES;

namespace HananRouter {

typedef long CostType;
const auto CostMax = std::numeric_limits<CostType>::max();
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

class CostFn {
  private:
    int _topRoutingLayer;
    std::vector<CostType> _layerHCost, _layerVCost;
    std::vector<std::vector<CostType>> _layerPairCost;
  public:
    CostType deltaCost(const Node& n1, const Node& n2) const;
    CostFn(const DRC::LayerInfo& lf);

    CostFn(const int numLayers = 0, const int minHLayer = 1, const int minVLayer = 0): _topRoutingLayer(numLayers - 1), _layerHCost(numLayers, 10000), _layerVCost(numLayers, 10000),
    _layerPairCost(numLayers, std::vector<CostType>(numLayers, 10000))
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
      //  std::cout << "layer : " << i << " cost : " << _layerHCost[i] << ' ' << _layerVCost[i] << '\n';
      //}
    }
};

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
      std::cout << s << ' ' << _x << ' ' << _y << ' ' << _z << ' ' << _fcost << ' ' << _tcost <<  ' ' << cost();
      if (_expanddir.test(NORTH)) std::cout << " N";
      if (_expanddir.test(SOUTH)) std::cout << " S";
      if (_expanddir.test(EAST))  std::cout << " E";
      if (_expanddir.test(WEST))  std::cout << " W";
      if (_expanddir.test(UP))    std::cout << " VU";
      if (_expanddir.test(DOWN))  std::cout << " VD";
      std::cout << '\n';
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
        return NodeComp()(n1, n2);
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
    std::vector<int> _widthx, _ndrwidthx, _spacex;
    std::vector<int> _widthy, _ndrwidthy, _spacey;
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
      CostType tcost = CostMax;
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
    bool isVert(const int l) const { return _lf.isVertical(l); }
    bool isHor(const int l) const { return _lf.isHorizontal(l); }
    void checkAndInsert(Node* newn, const Node* n);
    int snap(const Node* n, const bool vert, const bool up) const;
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
      std::cout << "flushing nodes\n";
#if DEBUG
      std::cout << " remaining " << Node::_nodectr << ' ' << _nodeset.size() << "\n";
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

    void constructVias();
    
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

    int widthx(const int z) const { return (_ndrwidthx[z] != INT_MAX ? std::max(_ndrwidthx[z], _widthx[z]) : _widthx[z]); }
    int widthy(const int z) const { return (_ndrwidthy[z] != INT_MAX ? std::max(_ndrwidthy[z], _widthy[z]) : _widthy[z]); }

    void clearSourceTargets() {
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
    }
    Geom::LayerRects findSol();
    void printSol() const;
    void plot() const;
    void writeSTO() const;
    void clearObstacles(bool temp = false)
    {
      if(temp) _tobstacles.clear();
      else _obstacles.clear();
    }
    void addObstacles(const Geom::LayerRects& lr, const bool temp = false);

    void addSourceTargetShapes(const Geom::Rect& r, const int z, const bool src);
    void addSourceShapes(const Geom::Rect& r, const int z) { addSourceTargetShapes(r, z, true); }
    void addTargetShapes(const Geom::Rect& r, const int z) { addSourceTargetShapes(r, z, false); }
    void addSourceTarget(const Geom::Rect& r, const int z, const bool src);
    void addSource(const Geom::Rect& r, const int z) { addSourceTarget(r, z, true); }
    void addTarget(const Geom::Rect& r, const int z) { addSourceTarget(r, z, false); }
    const Via* isViaValid(const Node* n, const bool up) const;
    void updatendr(const bool usendr);
    void setModName(const std::string& n) { _modname = n; }
    void setNetName(const std::string& n) { _netname = n; }
    void setuu(const int uu) { _uu = uu; }
    void writeLEF() const;
};

  void HananRoute(PnRDB::hierNode& node, const PnRDB::Drc_info& drcData, const int Lmetal, const int Hmetal);
}
#endif
