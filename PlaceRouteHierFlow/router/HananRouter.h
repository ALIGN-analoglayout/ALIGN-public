#ifndef HANAN_ROUTER_H_
#define HANAN_ROUTER_H_

#include <string>
#include <map>
#include <vector>
#include <string>
#include <climits>
#include <set>
#include <cmath>

#include <boost/geometry.hpp>
#include <boost/geometry/geometries/register/point.hpp>
#include <boost/geometry/geometries/register/box.hpp>
#include <boost/geometry/index/rtree.hpp>

#include "../PnRDB/datatype.h"

namespace bg = boost::geometry;
namespace bgi = boost::geometry::index;

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
    int getx() const { return _x; }
    int gety() const { return _y; }
    void setx(const int x) { _x = x; }
    void sety(const int y) { _y = y; }
    void scale(int t) { _x *= t; _y *= t; }
    void translate(int x, int y) { _x += x; _y += y; }
    void translate(int c) { _x += c; _y += c; }
    void translate(const Point& p) { _x += p.x(); _y += p.y(); }
    string toString() const { return to_string(_x) + "," + to_string(_y); }
    Point transform(const Transform& tr, const int width, const int height) const;
};

class Range {
  private:
    int _min, _max;
  public:
    Range(const int mn = INT_MAX, const int mx = INT_MIN) : _min(mn), _max(mx) {}
    const bool valid() const { return _min <= _max; }
    const bool overlaps(const Range& r) const { return _max >= r._min && r._max >= _min; }
    void merge(const Range& r)
    {
      _min = std::min(_min, r._min);
      _max = std::max(_max, r._max);
    }
    const int& min() const { return _min; }
    const int& max() const { return _max; }
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

    const Point& ll() const { return _ll; }
    const Point& ur() const { return _ur; }

    const bool xoverlap(const Rect& r) const { return xmin() <= r.xmax() && xmax() >= r.xmin(); }
    const bool yoverlap(const Rect& r) const { return ymin() <= r.ymax() && ymax() >= r.ymin(); }

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
    Rect bloated(const int cx, const int cy) { return Rect(xmin() - cx, ymin() - cy, xmax() + cx, ymax() + cy); }
    
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
      return r;
    }

    Rect transform(const Transform& tr, const int width, const int height) const;

    long area() const { return ((long)width()) * height(); }
    string toString() const { return _ll.toString() + " -- " + _ur.toString(); }

    int xdist(const Rect& r) const
    {
      return std::min(std::min(std::abs(r.xmin() - xmin()), std::abs(r.xmax() - xmax())),
          std::min(std::abs(r.xmin() - xmax()), std::abs(r.xmax() - xmin())));
    }
    int ydist(const Rect& r) const
    {
      return std::min(std::min(std::abs(r.ymin() - ymin()), std::abs(r.ymax() - ymax())),
          std::min(std::abs(r.ymin() - ymax()), std::abs(r.ymax() - ymin())));
    }
    int dist(const Rect&r, const bool euc = true) const
    {
      auto dx(xoverlap(r) ? 0 : xdist(r));
      auto dy(yoverlap(r) ? 0.: ydist(r));
      if (euc) return sqrt(dx * dx + dy * dy);
      return dx + dy;
    }
};

typedef vector<Rect> Rects;

}

BOOST_GEOMETRY_REGISTER_POINT_2D_GET_SET(geom::Point, int, bg::cs::cartesian, geom::Point::getx, geom::Point::gety, geom::Point::setx, geom::Point::sety);
BOOST_GEOMETRY_REGISTER_BOX(geom::Rect, geom::Point, geom::Rect::ll(), geom::Rect::ur());

namespace Hanan {

class Obj;

class Net {
  private:
    std::string _name;
    std::list<Obj*> _shapes;
  public:
    const std::string& name() const { return _name; }
    const std::list<Obj*> shapes() const { return _shapes; }
};

enum class ShapeType {
  PATH,
  VIA,
  PATH_OBS,
  VIA_OBS,
  MAX_SHAPE_TYPE
};

class Obj {
  private:
    geom::Rect _bbox;
    int _layer;
    const Net* _net;
    ShapeType _st;
  public:
    const geom::Rect& bbox() const { return _bbox; }
    int layer() const { return _layer; }
    Obj(const geom::Rect& r, const int l, const Net* net, const ShapeType& st) : _bbox(r), _layer(l), _net(net), _st(st) {}
    void setxmin(const int x) { _bbox.xmin() = x; }
    void setymin(const int y) { _bbox.ymin() = y; }
    void setxmax(const int x) { _bbox.xmax() = x; }
    void setymax(const int y) { _bbox.ymax() = y; }
    ShapeType shapeType() const { return _st; }
    bool isPath() const { return _st == ShapeType::PATH; }
    bool isVia() const { return _st == ShapeType::VIA; }
};

class Grid {
  private:
    const int _offset, _pitch;
    const std::vector<int> _pattern;
  public:
    Grid(const int offset, const int pitch, const vector<int>& pattern) : _offset(offset), _pitch(pitch), _pattern(pattern) {}
    bool isOnGrid(int p) const
    {
      if (p >= _offset && _pitch) {
        p = (p - _offset) % _pitch;
        for (const auto& x : _pattern) {
          if (x == p) return true;
        }
      }
      return false;
    }
    int snapUpToGrid(int p) const
    {
      if (p >= _offset && _pitch) {
        for (auto iter : {0, 1}) {
          auto delta = (p - _offset) % _pitch;
          unsigned i = 0;
          while (i < _pattern.size()) {
            if (delta == _pattern[i]) {
              return p;
            } else if (delta < _pattern[i]) {
              return p + _pattern[i] - delta;
            }
            ++i;
          }
          p += (_pitch - delta);
        }
      }
      return p;
    }
    int snapDnToGrid(int p) const
    {
      if (p >= _offset && _pitch) {
        for (auto iter : {0, 1}) {
          auto delta = (p - _offset) % _pitch;
          int i = _pattern.size() - 1;
          while (i >= 0) {
            if (delta == _pattern[i]) {
              return p;
            } else if (delta > _pattern[i]) {
              return p + _pattern[i] - delta;
            }
            --i;
          }
          p -= delta;
        }
      }
      return p;
    }
};

class Path : public Obj {
  public:
    Path(const geom::Rect& r, const int l, const Net* net) : Obj(r, l, net, ShapeType::PATH) {}
};

class Via : public Obj {
  private:
    const PnRDB::ViaModel* _viaModel;
  public:
    Via(const geom::Rect& r, const int l, const Net* net, const PnRDB::ViaModel* vm) : Obj(r, l, net, ShapeType::VIA), _viaModel(vm) {}
    int upperLayer() const { return _viaModel ? _viaModel->UpperIdx : -1; }
    int lowerLayer() const { return _viaModel ? _viaModel->LowerIdx : -1; }
    int viaLayer()   const { return _viaModel ? _viaModel->ViaIdx   : -1; }

};

typedef std::pair<geom::Rect, Obj*> bgVal;
typedef bgi::rtree<bgVal, bgi::quadratic<8, 4> > RTree;
class HRouterDB {
  private:
    vector<RTree> _metaltree, _viatree;

  public:
    HRouterDB() {}
    
};


void DetailRouter(PnRDB::hierNode& node, const PnRDB::Drc_info& drcData, const int Lmetal, const int Hmetal);
}

#endif
