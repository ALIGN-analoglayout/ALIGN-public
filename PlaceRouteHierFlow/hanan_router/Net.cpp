#include "Util.h"
#include "Placement.h"

#include <algorithm>

namespace Placement {

void Net::print() const
{
  COUT << "pins :";
  for (const auto& p : _pins) {
    std::cout << " " << p->name();
  }
  if (!_ndrwidths.empty()) {
    COUT << " ndr :";
    for (const auto& lw : _ndrwidths) {
      COUT << "(layer : " << lw.first << " width : " << lw.second << ") ";
    }
  }
  if (!_ndrvias.empty()) {
    COUT << " ndr via :";
    for (const auto& lv : _ndrvias) {
      COUT << "(layer : " << lv.first << " width : " << lv.second.str() << ") ";
    }
  }
}

PortPairs Net::reorderPorts() const
{
  PortCVec ports;
  for (auto virt : {true, false}) {
    auto& pins = virt ? _vpins : _pins;
    for (auto& p : pins) {
      ports.insert(ports.end(), p->ports().begin(), p->ports().end());
    }
  }
  PortPairs porder;
  if (ports.empty()) return porder;
  std::sort(ports.begin(), ports.end(),
      [](const Port* p1, const Port* p2) -> bool
      {
      const auto& b1 = p1->bbox();
      const auto& b2 = p2->bbox();
      if (b1.halfpm() == b2.halfpm()) {
      if (b1.ymin() == b2.ymin()) return b1.xmin() > b2.xmin();
      return b1.ymin() > b2.ymin();
      }
      return b1.halfpm() > b2.halfpm();
      }
      );
  std::vector< std::vector<double> > portpairdist(ports.size(), std::vector<double>(ports.size(), 0));
  double mindist{1e30};
  int idx1{-1}, idx2{-1};
  Geom::Rect netbbox;
  for (auto& p : ports) {
    netbbox.merge(p->bbox());
  }
  double nethpwl{(netbbox.width() + netbbox.height()) * 1.};
  for (unsigned i = 0; i < ports.size(); ++i) {
    auto& p1 = ports[i];
    auto& s1 = p1->shapes();
    for (unsigned j = i + 1; j < ports.size(); ++j) {
      auto& p2 = ports[j];
      double dist{1.e30};// = Geom::Dist(p1->bbox(), p2->bbox()) / nethpwl;
      auto& s2 = p2->shapes();
      for (auto& l1 : s1) {
        for (auto& r1 : l1.second) {
          for (auto& l2 : s2) {
            for (auto& r2 : l2.second) {
              dist = std::min(Geom::Dist(r1, r2)/nethpwl + std::abs(l1.first - l2.first) * 0.03, dist);
              /*if (ports[i]->isVirtualPort() || ports[j]->isVirtualPort()) {
                COUT << ports[i]->name() << ' ' << ports[j]->name() << ' ' <<  Geom::Dist(r1, r2) << ' ' << l1.first << ' ' << l2.first << ' ' << r1.str() << ' ' << r2.str() << ' ' << dist << '\n';
              }*/
            }
          }
        }
      }
      /*for (auto& l1 : s1) {
        auto its2 = s2.find(l1.first);
        if (its2 != s2.end()) {
          for (auto& r1 : l.second) {
            for (auto& r2 : its2->second) {
              dist = std::min(Geom::Dist(r1, r2)/nethpwl, dist);
            }
          }
        }
      }*/
      if (ports[i]->isVirtualPort() || ports[j]->isVirtualPort()) dist /= 10;
      portpairdist[i][j] = dist;
      portpairdist[j][i] = dist;
      COUT << "ports dist : " << ports[i]->name() << ' ' << ports[j]->name() << ' ' << dist << '\n';
      if (mindist > dist) {
        mindist = dist;
        idx1 = static_cast<int>(std::min(i, j));
        idx2 = static_cast<int>(std::max(i, j));
      } else if (mindist == dist) {
        if (idx1 > static_cast<int>(i)) {
          idx1 = static_cast<int>(std::min(i, j));
          idx2 = static_cast<int>(std::max(i, j));
        }
      }
    }
  }
  std::vector<std::pair<int, int>> primorder;
  primorder.reserve(ports.size() - 1);
  primorder.push_back(std::make_pair(idx1, idx2));
  COUT << "ports to route order : " << ports[idx1]->name() << ' ' << ports[idx2]->name() << '\n';
  std::vector<int> selected(ports.size(), 0);
  selected[idx1] = 1;
  selected[idx2] = 1;
  while (primorder.size() < ports.size() - 1) {
    double mindist{1e30};
    int minidx2 = -1, minidx1 = -1;
    for (int i = 0; i < static_cast<int>(ports.size()); ++i) {
      if (!selected[i]) continue;
      for (int j = 0; j < static_cast<int>(ports.size()); ++j) {
        if (!selected[j] && portpairdist[i][j] < mindist) {
          mindist = portpairdist[i][j];
          minidx1 = i;
          minidx2 = j;
        }
      }
    }
    if (minidx2 >= 0) {
      primorder.push_back(std::make_pair(minidx1, minidx2));
      COUT << "ports to route order : " << ports[minidx1]->name() << ' ' << ports[minidx2]->name() << '\n';
      selected[minidx2] = 1;
    }
  }

  std::sort(primorder.begin(), primorder.end(), [portpairdist](const std::pair<int, int>& a, const std::pair<int, int>& b) -> bool
      { return portpairdist[a.first][a.second] < portpairdist[b.first][b.second]; });

  
  for (auto& pp : primorder) porder.emplace_back(ports[pp.first], ports[pp.second]);

  return porder;
}

PortPairs Net::clockRouteOrder() const
{
  PortPairs porder;
  COUT << "clock net : " << _name << " with driver : " << _driver << '\n';
  const Pin* driver {nullptr};
  for (auto& p : _pins) {
    if (p->name() == _driver) {
      driver = p;
      break;
    }
  }
  if (driver != nullptr && !driver->ports().empty()) {
    for (unsigned j = 1; j < driver->ports().size(); ++j) {
      porder.push_back(std::make_pair(driver->ports()[0], driver->ports()[j]));
    }
    for (auto virt : {true, false}) {
      auto& pins = virt ? _vpins : _pins;
      for (auto& p : pins) {
        if (p == driver) continue;
        else {
          for (auto& port : p->ports()) {
            porder.push_back(std::make_pair(driver->ports()[0], port));
          }
        }
      }
    }
  }
  std::sort(porder.begin(), porder.end(),
      [](const PortPair& p1, const PortPair& p2) -> bool
      { return Geom::Dist(p1.first->bbox(), p1.second->bbox()) > Geom::Dist(p2.first->bbox(), p2.second->bbox()); }
      );
  for (auto& p : porder) {
    COUT << "ports to route order : " << p.first->name() << ' ' << p.second->name() << ' ' << Geom::Dist(p.first->bbox(), p.second->bbox()) << '\n';
  }
  return porder;
}

void Net::route(HRouter::Router& router, const Geom::LayerRects& l1, const Geom::LayerRects& l2, const Geom::LayerRects& l3, const bool update, const int uu, const Geom::Rect& bbox, const std::string& modname)
{
  //TIME_M();
#if DEBUG
  SaveRestoreStream src(_name + "_route.log");
#endif
  _unroute = 0;
  for (auto& pin : _pins) {
    for (auto& p : pin->ports()) {
      Geom::MergeLayerRects(_routeshapeswithpins, p->shapes(), &_bbox);
    }
  }
  if (router.debug()) {
    const Geom::LayerRects *obs[] = {&l1, &l2, &l3};
    writeLEF(modname, uu, bbox, obs);
  }
  if (_exclude) {
    COUT << "excluding net : " << _name << " from routing\n";
    return;
  }
  if (_pins.size() > 1) {
    COUT << "routing net : " << _name << ' ' << halfpm() << '\n';
    /*for (int i : {0, 1}) {
      for (auto& l : (i ? l1 : l2)) {
        for (auto& o : l.second) {
          COUT << "obs : " << l.first << ' ' << o.str() << '\n';
        }
      }
    }*/
    PortPairs ppairs = (_driver.empty() ? reorderPorts() : clockRouteOrder());
    for (auto& pp : ppairs) {
      const auto& port1 = pp.first;
      const auto& port2 = pp.second;
      router.clearSourceTargets();
      COUT << "routing ports : " << port1->name() << ' ' << port2->name() << '\n';
      router.setName(_name + "__" + port1->name() + "__" + port2->name());
      const auto& p1 = port1->shapes();
      const auto& p2 = port2->shapes();
      bool preflayersrctgt{true};
      Geom::LayerRects samenetobst;
      for (auto src : {true, false}) {
        bool preflayer{false};
        for (auto& l : _preflayers) {
          const auto& p = (src ? p1 : p2);
          auto it = p.find(l);
          if (it != p.end() && !it->second.empty()) {
            preflayer = true;
            break;
          }
        }
        preflayersrctgt &= preflayer;
        if (!_preflayers.empty()) {
          COUT << "pref layer pin" << (preflayer ? "" : " not") << " found for " << (src ? port1->name() : port2->name()) << '\n';
        }
        for (auto& l : (src ? p1 : p2)) {
          if (l.first > router.maxLayer() || l.first < router.minLayer()) {
            for (auto& s : l.second) samenetobst[l.first].push_back(s);
            continue;
          }
          if (preflayer && _preflayers.find(l.first) == _preflayers.end()) continue;
          //COUT << "port : " << (src ? port1->name() : port2->name()) << " layer " << l.first << '\n';
          for (auto& s : l.second) {
            if (src) {
              router.addSourceShapes(s, l.first);
            } else {
              router.addTargetShapes(s, l.first);
            }
          }
        }
      }
      router.updatendr(update, _ndrwidths, _ndrspaces, _ndrdirs, _preflayers, _ndrvias);
#if DEBUG
      COUT << "adding line of sight nodes if they exist\n";
#endif
      for (auto& l : p1) {
        auto it = p2.find(l.first);
        if (preflayersrctgt && _preflayers.find(l.first) == _preflayers.end()) continue;
        if (it != p2.end()) {
          for (auto& s1 : l.second) {
            for (auto& s2 : it->second) {
              if (s1.xmin() < s2.xmax() && s1.xmax() > s2.xmin()) {
                int xmin(std::max(s1.xmin(), s2.xmin())), xmax(std::min(s1.xmax(), s2.xmax()));
                if (xmax - xmin >= router.widthy(l.first)) {
                  router.addSource(Geom::Rect(xmin, s1.ymin(), xmax, s1.ymax()), l.first);
                  router.addTarget(Geom::Rect(xmin, s2.ymin(), xmax, s2.ymax()), l.first);
                }
              } else if (s1.ymin() < s2.ymax() && s1.ymax() > s2.ymin()) {
                int ymin(std::max(s1.ymin(), s2.ymin())), ymax(std::min(s1.ymax(), s2.ymax()));
                if (ymax - ymin >= router.widthx(l.first)) {
                  router.addSource(Geom::Rect(s1.xmin(), ymin, s1.xmax(), ymax), l.first);
                  router.addTarget(Geom::Rect(s2.xmin(), ymin, s2.xmax(), ymax), l.first);
                }
              }
            }
          }
        }
      }
      if (_detour) router.allowDetour();
      router.addObstacles(l1, true);
      router.addObstacles(l2, true);
      router.addObstacles(l3, true);
      router.addObstacles(_obstacles, true);
      router.addObstacles(samenetobst, true);
      auto sol = router.findSol();
      if (!sol.empty()) {
#if DEBUG
        for (auto& l : sol) {
          for (auto& s : l.second) {
            COUT << "sol : " << l.first << ' ' << s.str() << ' ' << s.width() << ' ' << s.height() << '\n';
          }
        }
#endif
        if (port1->isVirtualPort() || port2->isVirtualPort()) {
          for (auto i : {true, false}) {
            auto& port = i ? port1 : port2;
            if (port->isVirtualPort()) {
              auto& shapes = port->shapes();
              bool merged{false};
              for (auto& l : sol) {
                auto it = shapes.find(l.first);
                if (it != shapes.end()) {
                  for (auto& r : l.second) {
                    for (auto& rp : it->second) {
                      if (rp.overlaps(r)) {
                        if ((rp.ymin() == r.ymin() && rp.ymax() == r.ymax())
                            || (rp.xmin() == r.xmin() && rp.xmax() == r.xmax())) {
                          r.merge(rp);
                          merged = true;
                          break;
                        }
                      }
                    }
                  }
                  if (merged) break;
                }
                if (merged) break;
              }
            }
          }
        }
        Geom::MergeLayerRects(_routeshapeswithpins, sol, &_bbox);
        Geom::MergeLayerRects(_routeshapes, sol, &_bbox);
      } else {
        _unroute = 1;
      }
      if (!port1->isVirtualPort() || !_driver.empty()) {
        std::cout << "Adding routes to " << port1->name() << ' ' << sol.size() << std::endl;
        Geom::MergeLayerRects(const_cast<Geom::LayerRects&>(port1->shapes()), sol, &_bbox);
        if (port2->isVirtualPort()) {
          Geom::MergeLayerRects(const_cast<Geom::LayerRects&>(port1->shapes()), port2->shapes(), &_bbox);
          Geom::MergeLayerRects(_routeshapeswithpins, port2->shapes(), &_bbox);
          Geom::MergeLayerRects(_routeshapes, port2->shapes(), &_bbox);
        }
      }
      if (!port2->isVirtualPort() || !_driver.empty()) {
        std::cout << "Adding routes to " << port2->name() << ' ' << sol.size() << std::endl;
        Geom::MergeLayerRects(const_cast<Geom::LayerRects&>(port2->shapes()), sol, &_bbox);
        if (port1->isVirtualPort()) {
          Geom::MergeLayerRects(const_cast<Geom::LayerRects&>(port2->shapes()), port1->shapes(), &_bbox);
          Geom::MergeLayerRects(_routeshapeswithpins, port1->shapes(), &_bbox);
          Geom::MergeLayerRects(_routeshapes, port1->shapes(), &_bbox);
        }
      }
      router.clearObstacles(true);
    }
  }
}

void Net::writeLEF(const std::string& modname, const int uu, const Geom::Rect& bbox, const Geom::LayerRects* obs[]) const
{
  auto name(("net_" + modname + "_" + _name + ".lef"));
  COUT << "writing LEF file : " << name << "\n";
  std::ofstream ofs(name);
  if (ofs.is_open()) {
    ofs << "MACRO " << modname << "\n";
    ofs << "  UNITS\n    DISTANCE MICRONS " << uu << ";\n  END UNITS\n";
    ofs << "  ORIGIN "  << bbox.xmin()  << ' ' << bbox.ymin() << " ;\n";
    ofs << "  FOREIGN " << name << ' '  << (1.*bbox.xmin()/uu) << ' ' << (1.*bbox.ymin()/uu) << " ;\n";
    ofs << "  SIZE "    << (1.*bbox.width()/uu) << " BY " << (1.* bbox.height()/uu) << " ;\n";
    for (auto& v : {0, 1}) {
      for (auto& p : (v ? _pins : _vpins)) {
        ofs << "  PIN " << p->name() <<"\n    DIRECTION INOUT ;\n    USE SIGNAL ;\n";
        for (auto& pp : p->ports()) {
          ofs << "    PORT\n";
          for (auto& l : pp->shapes()) {
            ofs << "      LAYER " << LAYER_NAMES[l.first] << "_PIN ;\n";
            for (auto& r : l.second) {
              ofs << "        RECT " << (1.*r.xmin()/uu) << ' ' << (1.*r.ymin()/uu) << ' ' << (1.*r.xmax()/uu) << ' ' << (1.*r.ymax()/uu) << " ;\n";
            }
          }
          ofs << "      END\n";
        }
        ofs <<"  END " << p->name() << '\n';
      }
    }
    ofs << "  OBS\n";
    for (unsigned i = 0; i < 4; ++i) {
      if (obs[i]) {
        for (auto& l : (i < 3 ? *obs[i] : _obstacles)) {
          ofs << "      LAYER " << LAYER_NAMES[l.first] << " ;\n";
          for (auto r : l.second) {
            if (r.intersect(_bbox)) {
              ofs << "        RECT " << (1.*r.xmin()/uu) << ' ' << (1.*r.ymin()/uu) << ' ' << (1.*r.xmax()/uu) << ' ' << (1.*r.ymax()/uu) << " ;\n";
            }
          }
        }
      }
    }
    ofs << "    LAYER BBOX ;\n";
    ofs << "      RECT " << (1.*_bbox.xmin()/uu) << ' ' << (1.*_bbox.ymin()/uu) << ' ' << (1.*_bbox.xmax()/uu) << ' ' << (1.*_bbox.ymax()/uu) << " ;\n";
    ofs << "  END\n";
    ofs << "END " << modname << "\nEND LIBRARY\n";
  }
}

}
