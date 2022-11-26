#include <sstream>
#include "nlohmann/json.hpp"
#include "Util.h"
#include "Placement.h"
#include <cmath>
#include <sstream>

namespace Placement {
using json = nlohmann::json;
const auto& npos = std::string::npos;

Netlist::Netlist(const std::string& pldata, const::std::string& lefdata, const DRC::LayerInfo& lf, const int uu, const std::string& ndrfile) : _uu(uu), _valid{1}
{
  if (pldata.empty()) {
    _valid = 0;
    return;
  }
  std::istringstream ifs(pldata);
  if (!ifs) {
    _valid = 0;
    return;
  }
  auto oj = json::parse(ifs);
  auto it = oj.find("leaves");
  if (it != oj.end()) {
    for (auto& l : *it) {
      auto lname = l.find("concrete_name");
      if (_modules.find(*lname) != _modules.end()) continue;
      auto aname = l.find("abstract_name");
      if (lname != l.end()) {
        auto modu = new Module(*lname, (aname != l.end() ? *aname : *lname), 1, _uu);
        COUT << "adding leaf : " << *lname << '\n';
        auto terms = l.find("terminals");
        if (terms != l.end()) {
          for (auto& term : *terms) {
            auto p = modu->addPin(term["name"]);
            modu->addNet(term["name"]);
            modu->net(term["name"])->addPin(p);
          }
        }
        _modules[modu->name()] = modu;
      }
    }
  }
  it = oj.find("modules");
  if (it != oj.end()) {
    for (auto& m : *it) {
      auto mname = m.find("concrete_name");
      if (mname != m.end()) {
        if (_modules.find(*mname) != _modules.end()) continue;
        auto aname = m.find("abstract_name");
        auto modu = new Module(*mname, (aname != m.end() ? *aname : *mname), 0, _uu);
        auto params = m.find("parameters");
        COUT << "adding module : " << *mname << '\n';
        if (params != m.end()) {
          for (auto& p : *params) {
            modu->addPin(p);
          }
        }
        auto bbox = m.find("bbox");
        if (bbox != m.end()) {
          const auto& b = (*bbox);
          modu->setBBox(Geom::Rect(b[0], b[1], b[2], b[3]));
        }
        auto insts = m.find("instances");
        if (insts != m.end()) {
          for (auto& inst : *insts) {
            auto iname = inst.find("instance_name");
            auto mname = inst.find("concrete_template_name");
            auto tritr = inst.find("transformation");
            auto tr = (tritr == inst.end()) ? Geom::Transform() :
              Geom::Transform((*tritr)["oX"], (*tritr)["oY"], (*tritr)["sX"], (*tritr)["sY"]) ;
            Placement::Instance* instptr{nullptr};
            if (iname != inst.end() && mname != inst.end()) {
              instptr = modu->addInstance(*iname, *mname, tr);
            }
            if (instptr) {
              auto famap = inst.find("fa_map");
              if (famap != inst.end()) {
                for (auto& pm : *famap) {
                  const Net* n = &(modu->addNet(pm["actual"]));
                  modu->addTmpPin(n, instptr, pm["formal"]);
                }
              }
            } else {
              COUT << "instptr nullptr\n";
            }
          }
        }
        _modules[modu->name()] = modu;
      }
    }
  }
  loadLEFFromString(lefdata, lf);
  _loadedMacros.clear();
  build();
  readNDR(ndrfile, lf);
}


Netlist::~Netlist()
{
  for (auto& m : _modules) delete m.second;
  _modules.clear();
}


void Netlist::print() const
{
  for (const auto& m : _modules) {
    COUT << "module : " << m.second->name() << '\n';
    m.second->print();
  }
}


void Netlist::build()
{
  for (auto& m : _modules) {
    for (auto& inst : m.second->instances()) {
      auto it = _modules.find(inst->moduleName());
      if (it != _modules.end()) {
        inst->setModule(it->second);
      }
    }
  }
  for (auto& m : _modules) m.second->build();
}


void Netlist::loadLEFFromString(const std::string& lefdata, const DRC::LayerInfo& lf)
{
  if (lefdata.empty()) {
    _valid = 0;
    return;
  }
  std::istringstream ifs(lefdata);
  if (!ifs) {
    _valid = 0;
    return;
  }
  std::string line;
  bool inMacro{false}, inPin{false}, inObs{false}, inPort{false}, inUnits{false};
  Module* curr_module{nullptr};
  Pin* curr_pin{nullptr};
  Port* curr_port{nullptr};
  std::string macroName, pinName;
  int layer{-1};
  double macroUnits{1.};
  int units = _uu;
  while (std::getline(ifs, line)) {
    std::string str;
    std::stringstream ss(line);
    if (line.find("MACRO") != npos) {
      ss >> str >> macroName;
      COUT << "macro " << macroName << '\n';
      if (_loadedMacros.find(macroName) != _loadedMacros.end()) {
        while (std::getline(ifs, line)) {
          if (line.find("END") != npos && line.find(macroName) != npos) break;
        }
      }
      auto it = _modules.find(macroName);
      if (it != _modules.end()) {
        curr_module =  it->second;
        COUT << "loading macro " << macroName << '\n';
        _loadedMacros.insert(macroName);
      }
      inMacro = true;
      continue;
    }
    if (line.find("FOREIGN ") != npos) continue;
    if (line.find("END") != npos) {
      if (inUnits) {
        if (line.find("UNITS") != npos) {
          inUnits = false;
        }
      }
      if (inPort) {
        inPort = false;
        if (curr_port) curr_pin->addPort(curr_port);
        curr_port = nullptr;
      } else if (inPin) {
        if (line.find(pinName) != npos) {
          inPin = false;
          curr_pin = nullptr;
          pinName.clear();
        }
      } else if (inMacro) {
        if (line.find(macroName) != npos) {
          inMacro = false;
          curr_module = nullptr;
          macroName.clear();
        }
      } else if (inObs) {
        inObs = false;
        layer = -1;
      }
      continue;
    }
    if (inMacro && curr_module) {
      if (line.find("SIZE") != npos) {
        double w{0.}, h{0.};
        ss >> str >> w >> str >> h;
        curr_module->setBBox(Geom::Rect(0, 0, w * units, h * units));
      }
      if (line.find("PIN") != npos) {
        ss >> str >> pinName;
        curr_pin = curr_module->getPin(pinName);
        inPin = true;
        continue;
      }
    }
    if (inUnits && line.find("DATABASE") != npos) {
      ss >> str >> str >> str >> macroUnits;
      units /= macroUnits;
    }
    if (inPin && curr_pin && line.find("PORT") != npos) {
      inPort = true;
      curr_port = new Port();
      layer = -1;
      continue;
    }
    if (line.find("OBS") != npos) {
      inObs = true;
      continue;
    }
    if (inPort && curr_port) {
      if (line.find("LAYER") != npos) {
        ss >> str >> str;
        layer = lf.getLayerIndex(str);
        continue;
      }
      if (line.find("RECT") != npos) {
        double llx{0}, lly{0}, urx{0}, ury{0};
        ss >> str >> llx >> lly >> urx >> ury;
        if (layer >= 0) {
          curr_port->addRect(layer, Geom::Rect(round(llx * units), round(lly * units), round(urx * units), round(ury * units)));
        }
        continue;
      }
    }
    if (inObs && curr_module) {
      if (line.find("LAYER") != npos) {
        ss >> str >> str;
        layer = lf.getLayerIndex(str);
        if (str[0] != 'M' && str[0] != 'V') layer = -1;
        continue;
      }
      if (line.find("RECT") != npos) {
        double llx{0}, lly{0}, urx{0}, ury{0};
        ss >> str >> llx >> lly >> urx >> ury;
        if (layer >= 0) {
          curr_module->addObstacle(layer, Geom::Rect(round(llx * units), round(lly * units), round(urx * units), round(ury * units)));
        }
        continue;
      }
    }
  }
}

void Netlist::readNDR(const std::string& ndrfile, const DRC::LayerInfo& lf)
{
  if (!ndrfile.empty()) {
    std::ifstream ifs(ndrfile);
    if (!ifs) {
      CERR << "unable to open NDR file " << ndrfile <<std::endl;
      _valid = 0;
      return;
    }
    auto oj = json::parse(ifs);
    for (auto& m : oj) {
      auto it = m.find("module");
      if (it != m.end()) {
        auto modit = _modules.find(*it);
        if (modit != _modules.end()) {
          const std::vector<std::string> wsd = {"widths", "spaces", "directions", "preferred_layers", "vias"};
          for (unsigned iwsd = 0; iwsd < wsd.size(); ++iwsd) {
            auto itwsd = m.find(wsd[iwsd]);
            if (itwsd != m.end()) {
              if (iwsd < 3) {
                for (auto& el : (*itwsd).items()) {
                  auto layer = lf.getLayerIndex(el.key());
                  if (layer >= 0) {
                    switch (iwsd) {
                      default:
                      case 0: modit->second->addNDRWidth(layer, std::round(static_cast<double>(el.value()) * _uu));
                              break;
                      case 1: modit->second->addNDRSpace(layer, std::round(static_cast<double>(el.value()) * _uu));
                              break;
                      case 2: modit->second->addNDRDir(layer, el.value());
                              break;
                    }
                  }
                }
              } else if (iwsd == 3) {
                for (auto& el : (*itwsd)) {
                  auto layer = lf.getLayerIndex(el);
                  modit->second->addPrefLayer(layer);
                }
              } else if (iwsd == 4) {
                for (auto& el : (*itwsd).items()) {
                  auto layer = lf.getLayerIndex(el.key());
                  auto &via = el.value();
                  if (layer >= 0) {
                    int wx{0}, wy{0}, sx{0}, sy{0}, nx{0}, ny{0};
                    auto itvia = via.find("WidthX");
                    if (itvia != via.end()) wx = *itvia;
                    itvia = via.find("WidthY");
                    if (itvia != via.end()) wy = *itvia;
                    itvia = via.find("SpaceX");
                    if (itvia != via.end()) sx = *itvia;
                    itvia = via.find("SpaceY");
                    if (itvia != via.end()) sy = *itvia;
                    itvia = via.find("NumX");
                    if (itvia != via.end()) nx = *itvia;
                    itvia = via.find("NumY");
                    if (itvia != via.end()) ny = *itvia;
                    modit->second->addNDRVia(layer, DRC::ViaArray(wx, wy, sx, sy, nx, ny));
                  }
                }
              }
            }
          }
          it = m.find("nets");
          if (it != m.end()) {
            for (auto& netiter : *it) {
              auto itnetname = netiter.find("name");
              if (itnetname != netiter.end()) {
                auto itdetour = netiter.find("large_detour");
                if (itdetour != netiter.end() && *itdetour == "allowed") {
                  modit->second->allowDetour(*itnetname);
                }
                for (unsigned iwsd = 0; iwsd < wsd.size(); ++iwsd) {
                  auto itwsd = netiter.find(wsd[iwsd]);
                  if (itwsd != netiter.end()) {
                    if (iwsd < 3) {
                      for (auto& el : (*itwsd).items()) {
                        auto layer = lf.getLayerIndex(el.key());
                        if (layer >= 0) {
                          switch (iwsd) {
                            default:
                            case 0: modit->second->addNDRWidth(layer, std::round(static_cast<double>(el.value()) * _uu), *itnetname);
                                    break;
                            case 1: modit->second->addNDRSpace(layer, std::round(static_cast<double>(el.value()) * _uu), *itnetname);
                                    break;
                            case 2: modit->second->addNDRDir(layer, el.value(), *itnetname);
                                    break;
                          }
                        }
                      }
                    } else if (iwsd == 3) {
                      modit->second->clearPrefLayer(*itnetname);
                      for (auto& el : (*itwsd)) {
                        auto layer = lf.getLayerIndex(el);
                        modit->second->addPrefLayer(layer, *itnetname);
                      }
                    } else if (iwsd == 4) {
                      for (auto& el : (*itwsd).items()) {
                        auto layer = lf.getLayerIndex(el.key());
                        auto &via = el.value();
                        if (layer >= 0) {
                          int wx{0}, wy{0}, sx{0}, sy{0}, nx{0}, ny{0};
                          auto itvia = via.find("WidthX");
                          if (itvia != via.end()) wx = *itvia;
                          itvia = via.find("WidthY");
                          if (itvia != via.end()) wy = *itvia;
                          itvia = via.find("SpaceX");
                          if (itvia != via.end()) sx = *itvia;
                          itvia = via.find("SpaceY");
                          if (itvia != via.end()) sy = *itvia;
                          itvia = via.find("NumX");
                          if (itvia != via.end()) nx = *itvia;
                          itvia = via.find("NumY");
                          if (itvia != via.end()) ny = *itvia;
                          modit->second->addNDRVia(layer, DRC::ViaArray(wx, wy, sx, sy, nx, ny), *itnetname);
                        }
                      }
                    }
                  }
                }
              }
              auto itvpin = netiter.find("virtual_pins");
              if (itvpin != netiter.end()) {
                for (auto& vp : *itvpin) {
                  Geom::LayerRects lr;
                  for (auto& l : vp.items()) {
                    auto layer = lf.getLayerIndex(l.key());
                    if (layer >= 0) {
                      for (auto& r : l.value()) {
                        if (r.size() == 4) lr[layer].emplace_back(std::round(static_cast<double>(r[0]) * _uu), std::round(static_cast<double>(r[1]) * _uu),
                            std::round(static_cast<double>(r[2]) * _uu), std::round(static_cast<double>(r[3]) * _uu));
                      }
                    }
                  }
                  if (!lr.empty()) {
                    modit->second->addVirtualPin(*itnetname, lr);
                  }
                }
              }
            }
          }
          it = m.find("do_not_route");
          if (it != m.end()) {
            for (auto& netiter : *it) {
              modit->second->excludeNet(netiter);
            }
          }
          it = m.find("clock_nets");
          if (it != m.end()) {
            for (auto& netiter : *it) {
              auto itnetname = netiter.find("name");
              auto itdriver = netiter.find("driver");
              if (itnetname != netiter.end() && itdriver != netiter.end()) {
                modit->second->setClockDriver(*itnetname, *itdriver);
              }
            }
          }
          it = m.find("routing_order");
          if (it != m.end()) {
            for (auto& netiter : *it) {
              modit->second->addNetToOrder(netiter);
            }
          }
          it = m.find("obstacles");
          if (it != m.end()) {
            for (auto& obsiter : *it) {
              auto itnets = obsiter.find("nets");
              auto itshapes = obsiter.find("shapes");
              if (itshapes != obsiter.end()) {
                if (itnets == obsiter.end()) {
                  for (auto& l : (*itshapes).items()) {
                    auto layer = lf.getLayerIndex(l.key());
                    if (layer >= 0) {
                      for (auto& r : l.value()) {
                        if (r.size() == 4) {
                          COUT << "Adding obstacle to module " << modit->second->name() << " layer : " << l.key() << " : [" << r[0] << ' ' << r[1] << ' ' << r[2] << ' ' << r[3] << "]\n";
                          modit->second->addObstacle(layer, Geom::Rect(std::round(static_cast<double>(r[0]) * _uu), std::round(static_cast<double>(r[1]) * _uu),
                                std::round(static_cast<double>(r[2]) * _uu), std::round(static_cast<double>(r[3]) * _uu))); 
                        }
                      }
                    }
                  }
                } else {
                  for (auto& n : *itnets) {
                    for (auto& l : (*itshapes).items()) {
                      auto layer = lf.getLayerIndex(l.key());
                      if (layer >= 0) {
                        for (auto& r : l.value()) {
                          if (r.size() == 4) modit->second->addNetObstacle(n, layer, Geom::Rect(std::round(static_cast<double>(r[0]) * _uu), std::round(static_cast<double>(r[1]) * _uu),
                                std::round(static_cast<double>(r[2]) * _uu), std::round(static_cast<double>(r[3]) * _uu)));
                        }
                      }
                    }
                  }
                }
              }
            }
          }
          it = m.find("use_pin_width");
          if (it != m.end()) {
            modit->second->setusepinwidth(static_cast<int>(*it));
          }
        }
      }
    }
  }
}

}
