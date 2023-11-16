#include "Geom.h"
#include <cmath>
#include "RTree.h"

namespace Geom {

double Dist(const Geom::Rect& r1, const Geom::Rect& r2, const bool manh)
{
  double dist{0.};
  if (manh) {
    if (!r1.overlaps(r2)) {
      auto xdist{std::min(abs(r1.xmin() - r2.xmax()), abs(r1.xmax() - r2.xmin()))};
      if (r1.xmin() <= r2.xmax() && r2.xmin() <= r1.xmax()) xdist = 0;
      auto ydist{std::min(abs(r1.ymin() - r2.ymax()), abs(r1.ymax() - r2.ymin()))};
      if (r1.ymin() <= r2.ymax() && r2.ymin() <= r1.ymax()) ydist = 0;
      dist = (xdist + ydist);
    }
  } else {
    if (!r1.overlaps(r2)) {
      auto xdist{std::min(abs(r1.xmin() - r2.xmax()), abs(r1.xmax() - r2.xmin()))};
      if (r1.xmin() <= r2.xmax() && r2.xmin() <= r1.xmax()) xdist = 0;
      auto ydist{std::min(abs(r1.ymin() - r2.ymax()), abs(r1.ymax() - r2.ymin()))};
      if (r1.ymin() <= r2.ymax() && r2.ymin() <= r1.ymax()) ydist = 0;
      dist = sqrt(1.* xdist * xdist + 1. * ydist * ydist);
    }
  }
  return dist;
}

void MergeLayerRects(Geom::LayerRects& l1, const Geom::LayerRects& l2, Geom::Rect* b)
{
  for (auto& l : l2) {
    auto it = l1.find(l.first);
    if (it != l1.end()) {
      Rects cprects;
      for (const auto& s : l.second) {
        bool pushed{false};
        for (auto& t : it->second) {
          if (t.contains(s)) {
            pushed = true;
            continue;
          }
          if (s.contains(t)) {
            t = s;
            pushed = true;
            break;
          }
          if (t.overlaps(s)) {
            if (t.xmin() == s.xmin() && t.xmax() == s.xmax()) {
              t.ymin() = std::min(t.ymin(), s.ymin());
              t.ymax() = std::max(t.ymax(), s.ymax());
              pushed = true;
              break;
            } else if (t.ymin() == s.ymin() && t.ymax() == s.ymax()) {
              t.xmin() = std::min(t.xmin(), s.xmin());
              t.xmax() = std::max(t.xmax(), s.xmax());
              pushed = true;
              break;
            }
          }
        }
        if (!pushed) it->second.push_back(s);
      }
    } else {
      l1[l.first].insert(l1[l.first].end(), l.second.begin(), l.second.end());
    }
  }
  if (b != nullptr) {
    for (const auto& l : l2) {
      for (const auto& r : l.second) {
        b->merge(r);
      }
    }
  }
}

typedef RTree<int, int, 2, double, 16> Tree;

RTree2D::~RTree2D()
{
  if (nullptr != _rtree) {
    if (_copies) { 
      if (*_copies == 0) {
        delete static_cast<Tree*>(_rtree);
        delete _copies;
      } else {
        --(*_copies);
      }
    }
    _copies = nullptr;
    _rtree = nullptr;
  }
}

void RTree2D::insert(const Rect& r, const int i)
{
  if (nullptr == _rtree) _rtree = static_cast<void*>(new Tree);
  const int ll[] = {r.xmin(), r.ymin()};
  const int ur[] = {r.xmax(), r.ymax()};
  static_cast<Tree*>(_rtree)->Insert(ll, ur, i);
}

void RTree2D::remove(const Rect& r, const int i)
{
  if (_rtree) {
    const int ll[] = {r.xmin(), r.ymin()};
    const int ur[] = {r.xmax(), r.ymax()};
    static_cast<Tree*>(_rtree)->Remove(ll, ur, i);
  }
}

static bool callback(int i, void *arg)
{
  auto larg = static_cast<Rects**>(arg);
  larg[0]->push_back((*larg[1])[i]);
  return true;
}

int RTree2D::search(Rects& s, const Rect&r) const
{
  if (_rtree) {
    const int ll[] = {r.xmin(), r.ymin()};
    const int ur[] = {r.xmax(), r.ymax()};
    Rects* context[] = {&s, const_cast<Rects*>(&_rects)};
    return const_cast<Tree&>(*static_cast<Tree*>(_rtree)).Search(ll, ur, callback, static_cast<void*>(context));
  }
  return 0;
}
}
