#ifndef GEOM_H_
#define GEOM_H_
#include <string>
#include <map>
#include <vector>
#include <string>
#include <climits>
#include <set>
//#include "nlohmann/json.hpp"

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
    const int& x() const { return _x; }
    const int& y() const { return _y; }
    int& x() { return _x; }
    int& y() { return _y; }
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
    void snap(const int precx, const int precy, bool down) 
    {
      auto rx = (precx != 0) ? _x % precx : 0;
      auto ry = (precy != 0) ? _y % precy : 0;
      if (down) {
        if (rx != 0) _x -= rx;
        if (ry != 0) _y -= ry;
      } else {
        if (rx != 0) _x += (precx - rx);
        if (ry != 0) _y += (precy - ry);
      }
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

    void expand(const int c) { _ll.translate(-c); _ur.translate(c); }
    void expand(const int x, const int y) { _ll.translate(-x, -y); _ur.translate(x, y); }
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
        if (xmin() < r.xmax() && xmax() > r.xmin()
            && ymin() < r.ymax() && ymax() > r.ymin())
          return true;
      } else {
        if (xmin() <= r.xmax() && xmax() >= r.xmin()
            && ymin() <= r.ymax() && ymax() >= r.ymin())
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

    void snap(const int precx, const int precy)
    {
      _ll.snap(precx, precy, true);
      _ur.snap(precx, precy, false);
    }

    void snap(const int prec) { snap(prec, prec); }
    Rect snap(const int prec) const { auto x = Rect(_ll, _ur); x.snap(prec); return x; }
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

class RTree2D {
  private:
    const Rects& _rects;
    void* _rtree;
    unsigned* _copies;
  public:
    void insert(const Rect& r, const int i);
    RTree2D(const Rects& rects) : _rects{rects}, _rtree{nullptr}
    {
      for (unsigned i = 0; i < rects.size(); ++i) insert(rects[i], i);
      _copies = new unsigned(0);
    }
    RTree2D(const RTree2D& r) : _rects{r._rects}, _rtree{r._rtree}, _copies{r._copies}
    {
      ++(*_copies);
    }
    ~RTree2D();
    void remove(const Rect& r, const int i);
    int search(Rects& s, const Rect& r) const;
};
typedef map<int, RTree2D> LayerTree;

}
#endif
