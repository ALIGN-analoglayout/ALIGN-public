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
#include <boost/geometry/index/rtree.hpp>

#include "../PnRDB/datatype.h"

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

namespace HRouterDB {
}

namespace Hanan {

namespace bg = boost::geometry;
namespace bgi = boost::geometry::index;
typedef bg::model::point<int, 2, bg::cs::cartesian> bgPt;
typedef bg::model::box<bgPt> bgBox;
typedef std::pair<bgBox, size_t> bgVal;
typedef bgi::rtree<bgVal, bgi::quadratic<8, 4> > RTree;
void DetailRouter(PnRDB::hierNode& node, const PnRDB::Drc_info& drcData, const int Lmetal, const int Hmetal);
}

#endif
