#include "Util.h"
#include "Placement.h"

#include <algorithm>

namespace Placement {

void Port::print() const
{
  std::cout << "port : " << _name << '\n';
  for (const auto& l : _shapes) {
    std::cout << "\tlayer : " << l.first << '\n';
    for (const auto& r : l.second) {
      std::cout << "\t\t" << r.str() << '\n';
    }
  }
}

void Port::addRect(const int layer, const Geom::Rect& r)
{
  auto it = _shapes.find(layer);
  if (it != _shapes.end()) {
    bool pushed{false};
    for (auto& s : it->second) {
      if (r.contains(s)) {
        pushed = true;
        s = r;
        break;
      }
      if (s.contains(r)) {
        pushed = true;
        break;
      }
      if (r.overlaps(s)) {
        if (r.xmin() == s.xmin() && r.xmax() == s.xmax()) {
          s.ymin() = std::min(s.ymin(), r.ymin());
          s.ymax() = std::max(s.ymax(), r.ymax());
          pushed = true;
        } else if (r.ymin() == s.ymin() && r.ymax() == s.ymax()) {
          s.xmin() = std::min(s.xmin(), r.xmin());
          s.xmax() = std::max(s.xmax(), r.xmax());
          pushed = true;
        }
      }
    }
    if (!pushed) it->second.push_back(r);
  } else {
    _shapes[layer].push_back(r);
  }
  _bbox.merge(r);
}

Port* Port::getTransformedPort(const Geom::Transform& tr) const
{
  Port* port = new Port(_name);
  for (const auto& ls : _shapes) {
    for (const auto& s : ls.second) {
      port->_shapes[ls.first].push_back(tr.transform(s));
    }
  }
  port->_bbox = tr.transform(_bbox);
  return port;
}

void Pin::print() const
{
  std::cout << "pin : " << _name << '\n';
  for (auto& p : _ports) p->print();
}

Module::~Module()
{
  for (auto& p : _pins) delete p.second;
  for (auto& i : _instances) delete i;
  _pins.clear();
  _instances.clear();
}

void Module::print() const
{
  for (const auto& p : _pins) {
    p.second->print();
  }
  for (const auto& n : _nets) {
    COUT << "\tnet : " << n.first << " : {";
    n.second.print();
    std::cout << "}\n";
  }
  for (const auto& inst : _instances) {
    COUT << "\tinst : " ;
    inst->print("\t");
  }
  for (const auto& l : _obstacles) {
    COUT << "\tobstacle : layer : " << l.first;
    for (const auto& r : l.second) {
      std::cout << "\t\t" << r.str() << '\n';
    }
  }
  for (const auto& l : _internalroutes) {
    COUT << "\tinternal routes : layer : " << l.first;
    for (const auto& r : l.second) {
      std::cout << "\t\t" << r.str() << '\n';
    }
  }
}

void Module::build()
{
  for (auto& i : _instances) i->build();
  for (auto& t : _tmpnetpins) {
    for (auto& instpin : t.second) {
      auto it = instpin.first->_pins.find(instpin.second);
      if (it != instpin.first->_pins.end()) {
        const_cast<Net*>(t.first)->addPin(it->second);
      }
    }
  }
  _tmpnetpins.clear();
}

void Module::route(Router::Router& router, const std::string& outdir)
{
  TIME_M();
  if (!_routed) {
    router.setuu(_uu);
    //writeDEF("_before");
    router.clearObstacles();
    router.clearObstacles(true);
    for (auto& inst : _instances) {
      auto m = inst->module();
      if (!m->routed()) {
        const_cast<Module*>(m)->route(router, outdir);
      }
      inst->build(true);
      for (const auto& l : m->obstacles()) {
        for (const auto& r : l.second) {
          _obstacles[l.first].push_back(inst->transform(r));
        }
      }
      for (const auto& l : m->internalroutes()) {
        for (const auto& r : l.second) {
          _obstacles[l.first].push_back(inst->transform(r));
          _internalroutes[l.first].push_back(inst->transform(r));
        }
      }
    }
    updateNets();
    NetsVec nets;
    for (auto &n : _nets) {
      if (std::find(_routeorder.begin(), _routeorder.end(), &n.second) == _routeorder.end()) {
        nets.push_back(&n.second);
      }
    }
    std::sort(nets.begin(), nets.end(), [](const Net* a, const Net* b) -> bool
        { return a->halfpm() < b->halfpm(); });
    nets.insert(nets.begin(), _routeorder.begin(), _routeorder.end());
    COUT << " routing : " << _name << "; num nets : " << nets.size() << "; use pin width : " << ((_usepinwidth == 1) ? 1 : 0) << '\n';
    //router.addObstacles(_obstacles);
    Geom::LayerRects netObstaclesRouted, netObstaclesUnrouted;
    router.setModName(_name);
    COUT << "setting module name : " << _name << '\n';
    router.setusepinwidth((_usepinwidth == 1) ? true : false);
    static std::set<std::string> debugnet(splitString((getenv("HANAN_DEBUG_NET") ? std::string(getenv("HANAN_DEBUG_NET")) : std::string("")), ','));
    for (auto it = nets.begin(); it != nets.end(); ++it) {
      netObstaclesUnrouted.clear();
      for (auto itn = nets.begin(); itn != it; ++itn) {
        if ((*itn)->excluded()) {
          for (auto virt : {true, false}) {
            const auto& pins = virt ? (*itn)->virtualpins() : (*itn)->pins();
            for (auto& pin : pins) {
              for (auto& p : pin->ports()) {
                Geom::MergeLayerRects(netObstaclesUnrouted, p->shapes());
              }
            }
          }
        }
      }
      for (auto itn = std::next(it); itn != nets.end(); ++itn) {
        for (auto virt : {true, false}) {
          const auto& pins = virt ? (*itn)->virtualpins() : (*itn)->pins();
          for (auto& pin : pins) {
            for (auto& p : pin->ports()) {
              Geom::MergeLayerRects(netObstaclesUnrouted, p->shapes());
            }
          }
        }
      }
      router.setNetName((*it)->name());
      if (debugnet.find(_name + "__" + (*it)->name()) != debugnet.end()
          || debugnet.find((*it)->name()) != debugnet.end()
          || debugnet.find(_name) != debugnet.end()) {
        router.setEnableDebug(true);
      } else {
        router.setEnableDebug(false);
      }
      (*it)->route(router, netObstaclesRouted, netObstaclesUnrouted, _obstacles, true, _uu, _bbox, _name);
      //writeDEF("_" + (*it)->name(), (*it)->name());
      Geom::MergeLayerRects(netObstaclesRouted, (*it)->routeShapesWithPins());
    }
    router.clearObstacles();
    std::set<std::string> _addednets;
    for (auto& p : _pins) {
      auto itn = _nets.find(p.first);
      //std::cout << "DEBUG pin name " << p.first << '\n';
      if (itn != _nets.end()) {
        _addednets.insert(itn->first);
        //std::cout << "DEBUG found net : " << itn->second.name() << ' ' << itn->second.routeShapesWithPins().size() << '\n';
        if (!itn->second.excluded()) p.second->copyRects(itn->second.routeShapesWithPins());
        else {
          COUT << "excluded : " << itn->second.name() << "\n";
          for (auto& pin : itn->second.pins()) {
            COUT << "pin : " << pin->name() << '\n';
            for (auto& port : pin->ports()) {
              COUT << "port : " << port->name() << '\n';
              p.second->copyRects(port->shapes(), true);
            }
          }
        }
      }
    }
    for (auto& n : _nets) {
      if (_addednets.find(n.first) == _addednets.end()) {
        //std::cout << "unadded net : " << n.first << '\n';
        Geom::MergeLayerRects(_internalroutes, n.second.routeShapesWithPins());
      }
    }
    writeDEF(outdir);
  }
  if (!_leaf && !_top) {
    writeLEF(outdir);
  }
  _routed = 1;
  checkShort();
}

void Module::plot() const
{
  std::ofstream ofs(_name + ".gplt");
  if (ofs.is_open()) {
    COUT << "plotting module " << _name << " to " << _name << ".gplt\n";
    ofs << "unset key\n";
    ofs << "set title '" << _name << "' noenhanced\n";
    unsigned cnt{1};
    for (auto& l : _obstacles) {
      const auto& color = LAYER_COLORS[l.first % LAYER_COLORS.size()];
      for (auto& b : l.second) {
        if (b.valid() && b.width() && b.height()) {
          ofs << "set object " << cnt++ << " rect from ";
          ofs << b.xmin() << "," << b.ymin() << " to " << b.xmax() << "," << b.ymax() << " fillstyle transparent solid 0.25 fillcolor \"" << color << "\" behind\n";
        }
      }
    }
    for (const auto& p : _pins) {
      for (auto& port : p.second->ports()) {
        if (port->shapes().empty()) {
          auto& b = p.second->bbox();
          if (b.valid()) {
            ofs << "set object " << cnt++ << " rect from ";
            ofs << b.xmin() << "," << b.ymin() << " to " << b.xmax() << "," << b.ymax() << " fillcolor 'black' fillstyle pattern " << ((cnt % 2) + 5) << " transparent behind\n";
            ofs << "set label \"" << p.second->name() << "\" at " << b.xcenter() << "," << b.ycenter() << " center noenhanced\n";
          }
        }
      }
    }
    for (auto& n : _nets) {
      for (auto& l : n.second.routeShapesWithPins()) {
        for (auto& b : l.second) {
          const auto& color = LAYER_COLORS[l.first % LAYER_COLORS.size()];
          if (b.valid()) {
            //ofs << b.xmin() << " " << b.ymin() << "\n";
            //ofs << b.xmax() << " " << b.ymin() << "\n";
            //ofs << b.xmax() << " " << b.ymax() << "\n";
            //ofs << b.xmin() << " " << b.ymax() << "\n";
            //ofs << b.xmin() << " " << b.ymin() << "\n\n";
            ofs << "set object " << cnt++ << " rect from ";
            ofs << b.xmin() << "," << b.ymin() << " to " << b.xmax() << "," << b.ymax() << " fillstyle transparent solid 0.25 fillcolor \"" << color << "\" behind\n";
          }
        }
      }
    }
    for (auto& i : _instances) {
      auto& b = i->bbox();
      if (b.valid()) {
        ofs << "set label \"" << i->name() << "\" at " << b.xcenter() << "," << b.ycenter() << " center tc lt 3 font \",15\" noenhanced\n";
      }
      for (const auto& p : i->pins()) {
        auto& b = p.second->bbox();
        if (b.valid()) {
          ofs << "set object " << cnt++ << " rect from ";
          ofs << b.xmin() << "," << b.ymin() << " to " << b.xmax() << "," << b.ymax() << " fillcolor 'black' fillstyle pattern 2 transparent behind\n";
          ofs << "set label \"" << p.second->name() << "\" at " << b.xcenter() << "," << b.ycenter() << " center noenhanced\n";
        }
      }
    }
    auto& b = _bbox;
    ofs << "plot[:][:] '-' using 1:2 w l lt -1 lw 2 lc -1, '-' using 1:2 w l lt 1 lw 2 lc 1\n";
    if (b.valid()) {
      ofs << b.xmin() << " " << b.ymin() << "\n";
      ofs << b.xmax() << " " << b.ymin() << "\n";
      ofs << b.xmax() << " " << b.ymax() << "\n";
      ofs << b.xmin() << " " << b.ymax() << "\n";
      ofs << b.xmin() << " " << b.ymin() << "\n\n";
    }
    for (auto& i : _instances) {
      auto& b = i->bbox();
      if (b.valid()) {
        ofs << b.xmin() << " " << b.ymin() << "\n";
        ofs << b.xmax() << " " << b.ymin() << "\n";
        ofs << b.xmax() << " " << b.ymax() << "\n";
        ofs << b.xmin() << " " << b.ymax() << "\n";
        ofs << b.xmin() << " " << b.ymin() << "\n\n";
      }
    }
    ofs << "EOF\n";
    for (auto& n : _nets) {
      //if (!n.second.open()) continue;
      for (auto& p : n.second.pins()) {
        auto& b = p->bbox();
        if (b.valid()) {
          ofs << b.xcenter() << " " << b.ycenter() << "\n";
        }
      }
      ofs << "\n";
    }
    ofs << "EOF\n";
    ofs << "set size ratio GPVAL_DATA_Y_MAX/GPVAL_DATA_X_MAX\nrepl\npause -1";
  }
  ofs.close();
}

void Module::checkShort() const
{
  COUT << "Checking SHORT for module : " << _name << '\n';
  for (auto it1 = _nets.begin(); it1 != _nets.end(); ++it1) {
    for (auto it2 = std::next(it1); it2 != _nets.end(); ++it2) {
      auto& s1 = it1->second.routeShapesWithPins();
      auto& s2 = it2->second.routeShapesWithPins();
      for (auto& l : s1) {
        auto its2 = s2.find(l.first);
        if (its2 == s2.end()) continue;
        for (auto& o1 : l.second) {
          for (auto& o2 : its2->second) {
            if (o1.overlaps(o2)) {
              COUT << "SHORT between " << it1->second.name() << " & " << it2->second.name() << " @ layer : " << l.first << '\n';
              COUT << o1.str() << ' ' << o2.str() << '\n';
            }
          }
        }
      }
    }
  }
  for (auto it1 = _nets.begin(); it1 != _nets.end(); ++it1) {
    auto& s1 = it1->second.routeShapesWithPins();
    auto& s2 = _obstacles;
    for (auto& l : s1) {
      auto its2 = s2.find(l.first);
      if (its2 == s2.end()) continue;
      for (auto& o1 : l.second) {
        for (auto& o2 : its2->second) {
          if (o1.overlaps(o2)) {
            COUT << "SHORT between " << it1->second.name() << " & obstacle @ layer : " << l.first << '\n';
            COUT << o1.str() << ' ' << o2.str() << '\n';
          }
        }
      }
    }
  }
}

void Module::writeDEF(const std::string& outdir, const std::string& nstr, const std::string& netname) const
{
  std::ofstream ofs(outdir + _name + nstr + ".def");
  if (ofs.is_open()) {
    ofs << "VERSION 5.8 ;\nDIVIDERCHAR \"/\" ;\nBUSBITCHARS \"[]\" ;\nDESIGN " << _name << " ;\n";
    ofs << "UNITS DISTANCE MICRONS " << _uu << " ;\n";
    ofs << "DIEAREA ( " << _bbox.xmin() << ' ' << _bbox.ymin() << " ) ( " << _bbox.xmax() << ' ' << _bbox.ymax() << " ) ; \n\n";
    if (!_instances.empty() || !netname.empty()) {
      ofs << "COMPONENTS " << (_instances.size() + !netname.empty()) << " ;\n";
      for (auto& inst : _instances) {
        auto& tr = inst->transform();
        ofs << "- " << inst->name() << ' ' << inst->moduleName();
        ofs << " + PLACED ( ";
        ofs << ((tr.sX() > 0 ) ? tr.x() : (tr.x() - inst->bbox().width()))  << ' ';
        ofs << ((tr.sY() > 0 ) ? tr.y() : (tr.y() - inst->bbox().height())) << " ) " << tr.orient() << " ;\n";
      }
      if (!netname.empty()) {
        ofs << "- " << _name << '_' << netname << "_0 " << _name << '_' << netname;
        ofs << " + PLACED ( 0 0 ) N ;\n";
      }
      ofs << "END COMPONENTS\n\n";
    }
    if (!_nets.empty()) {
      ofs << "NETS " << _nets.size() << " ;\n ";
      for (auto& n : _nets) {
        ofs << "- " << n.first << "\n";
        for (auto& p : n.second.pins()) {
          std::string instname = p->name();
          std::string pinname  = p->name();
          auto ppos = p->name().rfind('+');
          if (ppos != std::string::npos) {
            instname = p->name().substr(0, ppos);
            pinname  = p->name().substr(ppos + 1);
          }
          ofs << " ( " << instname << ' ' << pinname << " )";
        }
        auto& routeShapes = n.second.routeShapes();
        if (!routeShapes.empty()) {
          ofs << "\n";
          for (auto& l : routeShapes) {
            for (auto& r : l.second) {
              ofs << "  + RECT " << LAYER_NAMES[l.first];
              ofs << " ( " << r.xmin() << ' ' << r.ymin() << " ) ( " << r.xmax() << ' ' << r.ymax() << " )\n";
            }
          }
        }
        ofs << " ;\n";
      }
      ofs << "END NETS\n\n";
    }
    /*if (!_internalroutes.empty()) {
      ofs << "FILLS " << _internalroutes.size() << " ;\n ";
      for (auto& l : _internalroutes) {
        ofs << "  - LAYER " << LAYER_NAMES[l.first] << "\n";
        for (unsigned i = 0; i < l.second.size(); ++i) {
          auto& r = l.second[i];
          ofs << "    RECT ( " << r.xmin() << ' ' << r.ymin() << " ) ( " << r.xmax() << ' ' << r.ymax() << " )";
          if (i == l.second.size() - 1) ofs << " ;\n";
          else ofs << "\n";
        }
      }
      ofs << "END FILLS\n\n";
    }*/
    ofs << "END DESIGN\n";
  }
}

void Module::writeLEF(const std::string& outdir) const
{
  std::ofstream ofs(outdir + _name + "_interim_hier.lef");
  if (ofs.is_open()) {
    ofs << "MACRO " << _name << "\n";
    ofs << "  UNITS\n    DISTANCE MICRONS " << _uu << ";\n  END UNITS\n";
    ofs << "  ORIGIN "  << _bbox.xmin()  << ' ' << _bbox.ymin() << " ;\n";
    ofs << "  FOREIGN " << _name << ' '  << (1.*_bbox.xmin()/_uu) << ' ' << (1.*_bbox.ymin()/_uu) << " ;\n";
    ofs << "  SIZE "    << (1.*_bbox.width()/_uu) << " BY " << (1.* _bbox.height()/_uu) << " ;\n";
    if (!_pins.empty()) {
      for (auto& pin : _pins) {
        ofs << "  PIN " << pin.first << "\n    DIRECTION INOUT ;\n    USE SIGNAL ;\n";
        for (auto& p : pin.second->ports()) {
          const auto& shapes = p->shapes();
          if (!shapes.empty()) {
            ofs << "    PORT\n";
            for (auto& l : shapes) {
              ofs << "      LAYER " << LAYER_NAMES[l.first] << " ;\n";
              for (auto& r : l.second) {
                ofs << "        RECT " << (r.xmin()*1.0/_uu) << ' ' << (1.*r.ymin()/_uu) << ' ' << (1.*r.xmax()/_uu) << ' ' << (1.*r.ymax()/_uu) << " ;\n";
              }
            }
            ofs << "    END\n";
          }
        }
        ofs << "  END " << pin.first << '\n';
      }
    }
    if (!_obstacles.empty() || !_internalroutes.empty()) {
      ofs << "    OBS\n";
      for (auto& l : _obstacles) {
        ofs << "      LAYER " << LAYER_NAMES[l.first] << " ;\n";
        for (auto& r : l.second) {
          ofs << "        RECT " << (1.*r.xmin()/_uu) << ' ' << (1.*r.ymin()/_uu) << ' ' << (1.*r.xmax()/_uu) << ' ' << (1.*r.ymax()/_uu) << " ;\n";
        }
      }
      for (auto& l : _internalroutes) {
        ofs << "      LAYER " << LAYER_NAMES[l.first] << " ;\n";
        for (auto& r : l.second) {
          ofs << "        RECT " << (1.*r.xmin()/_uu) << ' ' << (1.*r.ymin()/_uu) << ' ' << (1.*r.xmax()/_uu) << ' ' << (1.*r.ymax()/_uu) << " ;\n";
        }
      }
      ofs << "    END\n";
    }
    ofs << "END " << _name << "\n";
  }
}

}
