#ifndef PLACEMENT_H_
#define PLACEMENT_H_
#include <fstream>
#include "Geom.h"
#include "Layer.h"
#include "HananRouter.h"

namespace Placement {

class Module;
class Netlist;
class Instance;
typedef std::vector<Instance*> Instances;
typedef std::map<std::string, Module*> Modules;

class Port {
  private:
    std::string _name;
    Geom::LayerRects _shapes;
    Geom::Rect _bbox;
    unsigned int _virtual : 1;
  public:
    Port(const std::string& name = "", const bool virt = false) : _name{name}, _bbox{}, _virtual{static_cast<unsigned>(virt ? 1 : 0)} {}
    const std::string& name() const { return _name; }
    void setName(const std::string& name) { _name = name; }
    void addRect(const int layer, const Geom::Rect& r);
    const Geom::LayerRects& shapes() const { return _shapes; }
    const Geom::Rect& bbox() const { return _bbox; }
    void copyRects(const Geom::LayerRects& lr)
    {
      Geom::MergeLayerRects(_shapes, lr, &_bbox);
    }
    Port* getTransformedPort(const Geom::Transform& tr) const;
    void print() const;
    bool isVirtualPort() const { return _virtual ? true : false; }
};
typedef std::vector<Port*> Ports;
typedef std::vector<const Port*> PortCVec;
typedef std::pair<const Port*, const Port*> PortPair;
typedef std::vector<PortPair> PortPairs;

class Pin {
  private:
    std::string _name;
    Ports _ports;
    Geom::Rect _bbox;
    unsigned int _virtual : 1;
  public:
    Pin(const std::string& name = "", const bool virt = false) : _name{name}, _bbox{}, _virtual{static_cast<unsigned>(virt ? 1 : 0)} {}
    const std::string& name() const { return _name; }
    const Geom::Rect& bbox() const { return _bbox; }
    bool isVirtualPin() const { return _virtual ? true : false; }
    void print() const;
    void addPort(Port* p) 
    {
      if (p != nullptr)  {
        p->setName(_name + "_port_" + std::to_string(_ports.size()));
        _ports.push_back(p);
        _bbox.merge(p->bbox());
      }
    }
    void clearPorts() { for (auto& p : _ports) delete p; _ports.clear(); }
    ~Pin() { clearPorts(); }
    const Ports& ports() const { return _ports; }
    void copyRects(const Geom::LayerRects& lr, bool newport = false)
    {
      if (_ports.empty() || newport) {
        addPort(new Port("", isVirtualPin()));
      }
      _ports.back()->copyRects(lr);
    }
};
typedef std::map<std::string, Pin*> Pins;

class Net {
  private:
    std::string _name;
    std::set<const Pin*> _pins, _vpins;
    Geom::LayerRects _routeshapeswithpins, _routeshapes, _obstacles;
    HRouter::Vias _vias;
    Geom::Rect _bbox;
    unsigned int _unroute : 1;
    unsigned int _exclude : 1;
    unsigned int _detour : 1;
    PortPairs reorderPorts() const;
    PortPairs clockRouteOrder() const;
    std::map<int, int> _ndrwidths, _ndrspaces;
    std::map<int, DRC::Direction> _ndrdirs;
    std::set<int> _preflayers;
    std::string _driver;
    std::map<int, DRC::ViaArray> _ndrvias;
  public:
    Net(const std::string& name) : _name{name}, _bbox{}, _unroute{1}, _exclude{0}, _detour{0}, _driver{} {}
    ~Net()
    {
      for (auto& vp : _vpins) delete vp;
      _vpins.clear();
    }
    const std::set<const Pin*>& pins() const { return _pins; }
    const std::set<const Pin*>& virtualpins() const { return _vpins; }
    void addPin(const Pin* p) { _pins.insert(p); }
    void addVirtualPin(const Geom::LayerRects& r)
    {
      Pin *npin = new Pin(_name + "_vp_" + std::to_string(_vpins.size()), true);
      npin->copyRects(r);
      _vpins.insert(npin);
      COUT << "Net : " << _name << " : added virtual pin : ";
      npin->print();
    }
    void print() const;
    const std::string& name() const { return _name; }
    void route(HRouter::Router& r, const Geom::LayerRects& l1, const Geom::LayerRects& l2, const Geom::LayerRects& l3, const bool update, const int uu, const Geom::Rect& bbox, const std::string& modname);
    const Geom::LayerRects& routeShapesWithPins() const { return _routeshapeswithpins; }
    const Geom::LayerRects& routeShapes() const { return _routeshapes; }
    const Geom::Rect& bbox() const { return _bbox; }
    const bool open() const { return _unroute ? true : false; }
    void update()
    {
      for (auto virt : {true, false}) {
        auto& pins = virt ? _vpins : _pins;
        for (auto& pin : pins) {
          for (auto& p : pin->ports()) {
            for (auto& l : p->shapes()) {
              for (auto& s : l.second) {
                _bbox.merge(s);
              }
            }
          }
        }
      }
    }
    int halfpm() const { return _bbox.halfpm(); }
    void addNDRWidth(const int layer, const int width) { _ndrwidths[layer] = width; }
    void addNDRSpace(const int layer, const int space) { _ndrspaces[layer] = space; }
    void addNDRDir(const int layer, const std::string& dir)
    {
      if (dir == "O" || dir == "o") _ndrdirs[layer] = DRC::Direction::ORTHOGONAL;
      else if (dir == "H" || dir == "h") _ndrdirs[layer] = DRC::Direction::HORIZONTAL;
      else if (dir == "V" || dir == "v") _ndrdirs[layer] = DRC::Direction::VERTICAL;
    }
    void addPrefLayer(const int layer) { _preflayers.insert(layer); }
    void addNDRVia(const int layer, const DRC::ViaArray& v) { _ndrvias[layer] = v; }
    void clearPrefLayer() { _preflayers.clear(); }
    void exclude() { _exclude = 1; }
    void allowDetour() { _detour = 1; }
    bool excluded() const { return _exclude ? true : false; }
    void setClockDriver(const std::string& driver) { _driver = driver; }
    void addObstacle(const int layer, const Geom::Rect& r) {
      COUT << "Adding obstacle to net : " << _name << " layer : " << layer << ' ' << r.str() << '\n';
      _obstacles[layer].push_back(r);
    }
    void writeLEF(const std::string& modname, const int uu, const Geom::Rect& bbox, const Geom::LayerRects* obs[]) const;
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
    HRouter::Vias _vias;
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
};


class Module {
  friend class Netlist;
  private:
    std::string _name, _absname;
    unsigned int _leaf : 1;
    unsigned int _routed : 1;
    unsigned int _usepinwidth : 1;
    Nets _nets;
    Pins _pins;
    Instances _instances;
    HRouter::Vias _vias;
    std::map<const Net*, std::vector<std::pair<Instance*, std::string>>> _tmpnetpins;
    Geom::LayerRects _obstacles, _internalroutes;
    Geom::Rect _bbox;
    const int _uu;
    NetsVec _routeorder;

    void build();
  public:
    Module(const std::string& name, const std::string& absname, const unsigned leaf, const int uu) : _name(name), _absname{absname}, _leaf(leaf), _routed{leaf}, _usepinwidth{0}, _bbox{}, _uu{uu} {_instances.reserve(64);}
    ~Module();
    Instance* addInstance(const std::string& name, const std::string& mname, const Geom::Transform& tr)
    {
      _instances.emplace_back(new Instance(name, mname, tr)); 
      return _instances.back();
    }
    bool routed() const { return (_routed ? true : false); }
    const std::string& absname() const { return _absname; }
    const std::string& name() const { return _name; }
    const Instances& instances() const { return _instances; }
    Instances& instances() { return _instances; }
    const Geom::LayerRects& obstacles() const { return _obstacles; }
    const Geom::LayerRects& internalroutes() const { return _internalroutes; }
    bool isLeaf() const { return _leaf ? true : false; }
    void setLeaf() { _leaf = 1; _routed = 1; }
    const Nets& nets() const { return _nets; }
    const Pins& pins() const { return _pins; }

    void setBBox(const Geom::Rect& b) { _bbox = b; }
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
      return (it != _nets.end()) ? &(it->second) : nullptr;
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
    void addObstacle(const int layer, const Geom::Rect& r) { _obstacles[layer].push_back(r); }
    void updateNets()
    {
      for (auto& n : _nets) {
        n.second.update();
      }
    }

    void addNDRWidth(const int layer, const int ws, const std::string& netName = "")
    {
      if (netName.empty()) {
        for (auto& itn : _nets) itn.second.addNDRWidth(layer, ws);
      } else {
        auto n = net(netName);
        if (n) n->addNDRWidth(layer, ws);
      }
    }
    void addNDRSpace(const int layer, const int ws, const std::string& netName = "")
    {
      if (netName.empty()) {
        for (auto& itn : _nets) itn.second.addNDRSpace(layer, ws);
      } else {
        auto n = net(netName);
        if (n) n->addNDRSpace(layer, ws);
      }
    }
    void addNDRDir(const int layer, const std::string& d, const std::string& netName = "")
    {
      if (netName.empty()) {
        for (auto& itn : _nets) itn.second.addNDRDir(layer, d);
      } else {
        auto n = net(netName);
        if (n) n->addNDRDir(layer, d);
      }
    }
    void clearPrefLayer(const std::string& netName) 
    {
      auto n = net(netName);
      if (n) n->clearPrefLayer();
    }
    void addPrefLayer(const int layer, const std::string& netName = "")
    {
      if (netName.empty()) {
        for (auto& itn : _nets) itn.second.addPrefLayer(layer);
      } else {
        auto n = net(netName);
        if (n) n->addPrefLayer(layer);
      }
    }
    void addNDRVia(const int layer, const DRC::ViaArray& v, const std::string& netName = "")
    {
      if (netName.empty()) {
        for (auto& itn : _nets) itn.second.addNDRVia(layer, v);
      } else {
        auto n = net(netName);
        if (n) n->addNDRVia(layer, v);
      }
    }
    void allowDetour(const std::string& netName)
    {
      auto n = net(netName);
      if (n) n->allowDetour();
    }

    void excludeNet(const std::string& netName)
    {
      auto n = net(netName);
      if (n) COUT << "excluding net : " << n->name() << " from routing\n";
      if (n) n->exclude();
    }

    void setClockDriver(const std::string& netName, const std::string& driver)
    {
      auto n = net(netName);
      if (n) n->setClockDriver(driver);
    }

    void addVirtualPin(const std::string& netName, const Geom::LayerRects& r)
    {
      auto n = net(netName);
      if (n) n->addVirtualPin(r);
    }

    void addNetToOrder(const std::string& netName)
    {
      auto n = net(netName);
      if (nullptr != n) _routeorder.push_back(n);
    }

    void addNetObstacle(const std::string& netName, const int layer, const Geom::Rect& r)
    {
      auto n = net(netName);
      if (nullptr != n) n->addObstacle(layer, r);
    }

    void setusepinwidth(int u) { _usepinwidth = u ? 1 : 0; }

    void print() const;
    void route(HRouter::Router& r, const std::string& outdir);
    void plot() const;

    const Geom::Rect& bbox() const { return _bbox; }
    void checkShort() const;

    void writeDEF(const std::string& outdir, const std::string& nstr = "", const std::string& netname = "") const;
    void writeLEF(const std::string& outdir) const;

};


class Netlist {
  private:
    const int _uu;
    int _valid;
    Modules _modules;
    void build();
    void loadLEFFromString(const std::string& lefdata, const DRC::LayerInfo& lf);
    void readNDR(const std::string& ndrfile, const DRC::LayerInfo& lf);
    std::set<std::string> _loadedMacros;

  public:
    Netlist(const std::string& pldata, const std::string& lefdata, const DRC::LayerInfo& lf, const int uu, const std::string& ndrfile = "");
    ~Netlist();
    void print() const;
    void route(HRouter::Router& r, const std::string& outdir)
    {
      if (!_valid) return;
      for (auto& m : _modules) m.second->route(r, outdir);
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
    void writeDEF(const std::string& outdir) const
    {
      if (!_valid) return;
      for (auto& m : _modules) if (!m.second->isLeaf()) m.second->writeDEF(outdir);
    }
};


}
#endif
