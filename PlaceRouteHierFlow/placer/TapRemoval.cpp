#include "TapRemoval.h"
#include <sstream>
#include <iterator>
#include <fstream>
#include "spdlog/spdlog.h"

#include <boost/geometry.hpp>
#include <boost/geometry/index/rtree.hpp>

namespace bg = boost::geometry;
namespace bgi = boost::geometry::index;
typedef bg::model::point<int, 2, bg::cs::cartesian> bgPt;
typedef bg::model::box<bgPt> bgBox;
typedef std::pair<bgBox, size_t> bgVal;
typedef bgi::rtree<bgVal, bgi::quadratic<8, 4> > RTree;

using namespace std;
typedef std::vector<std::string> Strings;

static Strings splitString(const std::string& s)
{
  Strings strs;
  std::istringstream iss(s);
  std::string tmps;
  while (iss >> tmps) {
    strs.push_back(tmps);
  }
  return move(strs);
}


namespace geom {

Point Point::transform(const Transform& tr, const int width, const int height) const
{
  Point p(_x, _y);
  if (tr.hflip()) p._x = width - p._x;
  if (tr.vflip()) p._y = height - p._y;
  p.translate(tr.origin());
  return p;
}

Rect Rect::transform(const Transform& tr, const int width, const int height) const
{
  return Rect(_ll.transform(tr, width, height), _ur.transform(tr, width, height));
}

}

namespace PrimitiveData {

Instance::Instance(const Primitive* prim, const Primitive* primWoTap, const string& name, const Transform& tr, const int& ind) :
_prim(prim), _primWoTap(primWoTap), _name(name), _bbox(Rect()), _woTapIndex(ind)
{
  if (_prim) {
    for (auto nmos : {true, false}) {
      auto& taps = nmos ? _ntaps : _ptaps;
      auto& actives = nmos ? _nactives : _pactives;
      for (const auto& t : _prim->getTaps(nmos)) {
        taps.push_back(t.transform(tr, _prim->width(), _prim->height()));
      }
      for (const auto& r : _prim->getActives(nmos)) {
        actives.push_back(r.transform(tr, _prim->width(), _prim->height()));
      }
    }
    _bbox = _prim->bbox().transform(tr, _prim->width(), _prim->height());
  }
}

void Instance::print() const
{
  auto logger = spdlog::default_logger()->clone("placer.Instance.print");
  logger->info("{0} {1} {2}", _name, _prim->name(), _primWoTap->name());
  logger->info("ntaps : ");
  for (auto& t : _ntaps) {
    logger->info("{0}", t.toString());
  }
  logger->info("nactives : ");
  for (auto& r : _nactives) {
    logger->info("{0}", r.toString());
  }
  logger->info("ptaps : ");
  for (auto& t : _ptaps) {
    logger->info("{0}", t.toString());
  }
  logger->info("pactives : ");
  for (auto& r : _pactives) {
    logger->info("{0}", r.toString());
  }
}

}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// namespace for classes/routines to find the dominating set of tap nodes in a graph
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
namespace DomSetGraph {
using namespace std;

Graph::Graph()
{
  _nodes.reserve(1024);
  _edges.reserve(1024);
}

Graph::~Graph()
{
  for (auto& e : _edges) delete e;
  _edges.clear();
  _edgeMap.clear();

  for (auto& v : _nodes) delete v;
  _nodes.clear();
  _nodeMap.clear();
}

void Graph::addNode(const string& name, const NodeType& nt, const long& da, const bool isb, const int dist)
{
  if (_nodeMap.find(name) != _nodeMap.end()) return;
  Node *n = new Node(name, nt, da, isb, dist);
  _nodes.push_back(n);
  _nodeMap[name] = n;
}

void Graph::addEdge(const string& un, const string& vn, const string& name)
{
  NodeMap::iterator it = _nodeMap.find(un);
  Node* u = (it != _nodeMap.end()) ? it->second : nullptr;
  it = _nodeMap.find(vn);
  Node* v = (it != _nodeMap.end()) ? it->second : nullptr;
  if (u != nullptr && v != nullptr) {
    if (_edgeMap.find(make_pair(u, v)) != _edgeMap.end() ||
          _edgeMap.find(make_pair(v, u)) != _edgeMap.end()) return;
    Edge *e = new Edge(u, v, name);
    _edges.push_back(e);
    u->addEdge(e);
    v->addEdge(e);
    _edgeMap[make_pair(u, v)] = e;
  }
}

const Edge* Graph::findEdge(const string& un, const string& vn) const
{
  Edge* e(nullptr);
  NodeMap::const_iterator it = _nodeMap.find(un);
  const Node* u = (it != _nodeMap.end()) ? it->second : nullptr;
  it = _nodeMap.find(vn);
  const Node* v = (it != _nodeMap.end()) ? it->second : nullptr;
  if (u != nullptr && v != nullptr) {
    EdgeMap::const_iterator ite = _edgeMap.find(make_pair(u, v));
    if (ite != _edgeMap.end()) e = ite->second;
    else {
      EdgeMap::const_iterator ite = _edgeMap.find(make_pair(v, u));
      if (ite != _edgeMap.end()) e = ite->second;
    }
  }
  return e;
}

void Graph::print() const
{
  /*cout << "# Graph " << endl;
  for (auto& n : _nodes) {
    cout << "Node " << n->toString() << endl;
    for (auto& e : n->edges()) {
      cout << "  # Edge " << e->toString() << endl;
    }
  }
  for (auto& e : _edges) {
    cout << "Edge " << e->toString() << endl;
    cout << "  # u : " << e->u()->toString() << endl;
    cout << "  # v : " << e->v()->toString() << endl;
  }*/
}

NodeSet Graph::dominatingSet() const
{
  auto logger = spdlog::default_logger()->clone("PnRDB.TapRemoval.dominatingSet");
  NodeSet whiteNodes, dom;
  size_t isoActive(0);
  for (auto& n : _nodes) {
    //logger->info("node : {0} {1}", n->name(), n->isBlack());
    if (n->isBlack()) {
      dom.insert(n);
      const_cast<Node*>(n)->setColor(NodeColor::Black);
      for (auto& e : n->edges()) {
        const Node* nbr = (e->v() == n) ? e->u() : e->v();
        if (NodeColor::Black != nbr->nodeColor()) {
          const_cast<Node*>(nbr)->setColor(NodeColor::Gray);
        }
      }
    }
  }
  for (auto& n : _nodes) {
    bool foundTap(false);
    if (n->nodeType() == NodeType::Tap) {
      foundTap = true;
    } else {
      for (auto& e : n->edges()) {
        const Node* nbr = (e->v() == n) ? e->u() : e->v();
        if (nbr && nbr->nodeType() == NodeType::Tap) {
          foundTap = true;
          break;
        }
      }
    }
    if (foundTap) {
      if (NodeColor::White == n->nodeColor()) {
        whiteNodes.insert(n);
      }
    } else ++isoActive;
    //logger->info("num edges {0}", n->edges().size());
    //for (auto& e : n->edges()) {
    ////logger->info("edge : {0} {1} {2}", e->name(), e->u()->name(), e->v()->name());
    //}
  }


  while (!whiteNodes.empty()) {
    //logger->info("white nodes : {0}", whiteNodes.size());
    for (auto& n : _nodes) {
      unsigned span(0);
      if (whiteNodes.find(n) != whiteNodes.end()) ++span;
      for (auto& e : n->edges()) {
        if (e->u() == n && whiteNodes.find(e->v()) != whiteNodes.end()) {
          ++span;
        }
        if (e->v() == n && whiteNodes.find(e->u()) != whiteNodes.end()) {
          ++span;
        }
      }
      n->setSpan(span);
    }
    unsigned maxW(0);
    for (auto& n : _nodes) {
      if (n->nodeType() != NodeType::Tap) continue;
      if (maxW < n->span()) {
        maxW = n->span();
      }
    }
    NodeSet maxNbrWhites;
    for (auto& n : _nodes) {
      if (n->nodeType() != NodeType::Tap) continue;
      if (n->span() == maxW) {
        maxNbrWhites.insert(n);
        auto it = _nodeSymPairs.find(n);
        if (it != _nodeSymPairs.end()) {
          //logger->info("sym pair {0} {1}", n->name(), it->second->name());
          maxNbrWhites.insert(it->second);
        }
      }
    }

    for (auto& n : maxNbrWhites) {
      if (NodeColor::White == n->nodeColor()) {
        dom.insert(n);
        auto it = _nodeSymPairs.find(n);
        if (it != _nodeSymPairs.end()) {
          dom.insert(it->second);
          const_cast<Node*>(it->second)->setColor(NodeColor::Black);
        }
      }
      const_cast<Node*>(n)->setColor(NodeColor::Black);
      for (auto& e : n->edges()) {
        const Node* nbr = (e->v() == n) ? e->u() : e->v();
        if (NodeColor::Black != nbr->nodeColor()) {
          const_cast<Node*>(nbr)->setColor(NodeColor::Gray);
        }
      }
    }

    for (auto& n : _nodes) {
      if (n->nodeColor() != NodeColor::White) whiteNodes.erase(n);
    }
  }

  //logger->info("dom size : {0}", dom.size());
  return dom;
}

void Graph::addSymPairs(const std::map<std::string, std::string>& counterparts)
{
  for (auto& n : _nodes) {
    if (n->nodeType() != NodeType::Tap) continue;
    std::string name;
    auto pos = n->name().rfind("__tap_");
    if (pos != std::string::npos) name = n->name().substr(0, pos);
    if (!name.empty()) {
      auto cit = counterparts.find(name);
      if (cit != counterparts.end()) {
        NodeMap::iterator nit = _nodeMap.find(cit->second + n->name().substr(pos));
        Node* u = (nit != _nodeMap.end()) ? nit->second : nullptr;
        if (u != nullptr) {
          _nodeSymPairs[n] = u;
        }
      }
    }
  }
}

}

void TapRemoval::buildGraph(const std::map<std::string, std::string>& counterparts)
{
  auto logger = spdlog::default_logger()->clone("placer.TapRemoval.buildGraph");
  RTree rtree;
  map<string, geom::Rect> allTaps;
  if (_graph == nullptr) _graph = new DomSetGraph::Graph;
  for (const auto& inst : _instances) {
    for (auto nmos : {true, false}) {
      const string mosString = nmos ? "__tr_nmos_" : "__tr_pmos_";
      auto& taps = inst->getTaps(nmos);
      for (unsigned i = 0; i < taps.size(); ++i) {
        bgBox b(bgPt(taps[i].xmin(), taps[i].ymin()), bgPt(taps[i].xmax(), taps[i].ymax()));
        rtree.insert(bgVal(b, _graph->nodes().size()));
        string nodeName(inst->name() + "__tap_" + mosString + to_string(i));
        allTaps[nodeName] = taps[i];
        _graph->addNode(nodeName, DomSetGraph::NodeType::Tap, inst->deltaArea(), inst->isBlack(), taps[i].ydist(_bbox));
      }
      auto& actives = inst->getActives(nmos);
      for (unsigned i = 0; i < actives.size(); ++i) {
        bgBox b(bgPt(actives[i].xmin(), actives[i].ymin()), bgPt(actives[i].xmax(), actives[i].ymax()));
        rtree.insert(bgVal(b, _graph->nodes().size()));
        _graph->addNode(inst->name() + "__active_" + mosString + to_string(i), DomSetGraph::NodeType::Active, inst->deltaArea());
      }
    }
  }

  //cout << allTaps.size() << endl;

  for (auto& it : allTaps) {
    bool pmosTap = it.first.find("__tr_pmos_") != std::string::npos;
    auto r = it.second.bloated(_dist);
    bgBox box(bgPt(r.xmin(), r.ymin()), bgPt(r.xmax(), r.ymax()));
    vector<bgVal> overlapRects;
    rtree.query(bgi::covered_by(box), back_inserter(overlapRects));
    for (auto& val : overlapRects) {
      auto& rname = _graph->nodes()[val.second]->name();
      bool pmosNbr = rname.find("__tr_pmos_") != std::string::npos;
      bool addRect(pmosTap == pmosNbr);
      if (pmosTap && pmosNbr) {
        auto minx = std::min(it.second.xmin(), val.first.min_corner().get<0>());
        auto miny = std::min(it.second.ymin(), val.first.min_corner().get<1>());
        auto maxx = std::max(it.second.xmax(), val.first.max_corner().get<0>());
        auto maxy = std::max(it.second.ymax(), val.first.max_corner().get<1>());
        vector<bgVal> rects;
        rtree.query(bgi::intersects(bgBox(bgPt(minx, miny), bgPt(maxx, maxy))), back_inserter(rects));
        for (auto& r : rects) {
          auto& rn= _graph->nodes()[r.second]->name();
          if (rn.find("__tr_pmos_") == std::string::npos) {
            addRect = false;
            break;
          }
        }
      }
      if (it.first != rname && addRect) {
        //cout << it.first << ' ' << rname << endl;
        _graph->addEdge(it.first, rname);
      }
    }
  }
  _graph->addSymPairs(counterparts);
}

TapRemoval::TapRemoval(const PnRDB::hierNode& node, const unsigned dist) : _dist(dist), _name(node.name), _graph(nullptr)
{
  auto logger = spdlog::default_logger()->clone("placer.TapRemoval.TapRemoval");
  for (unsigned i = 0; i < node.Blocks.size(); ++i) {
    if (node.Blocks[i].instance.empty()) continue;
    const auto& master=node.Blocks[i].instance.back().master;
    if (_primitives.find(master) != _primitives.end() ||
        _primitivesWoTap.find(master) != _primitivesWoTap.end()) continue;
    for (unsigned j = 0; j < node.Blocks[i].instance.size(); ++j) {
      const auto& n = node.Blocks[i].instance[j];
      PrimitiveData::Primitive *p(nullptr);
      //logger->info("node {0} {1} {2} {3}", n.name, i, j, n.HasTap());

      if (n._taVias) {
        p = new PrimitiveData::Primitive(master, geom::Rect(n.originBox));
        for (auto nmos : {true, false}) {
          const auto& tapVias = nmos ? n._taVias->_ntapVias : n._taVias->_ptapVias;
          const auto& activeVias = nmos ? n._taVias->_nactiveVias : n._taVias->_pactiveVias;
          for (const auto& t : tapVias) p->addTap(geom::Rect(t), nmos);
          for (const auto& t : activeVias) p->addActive(geom::Rect(t), nmos);
        }
      } else {
        continue;
      }

      if (!n._taVias->_ntapVias.empty() || !n._taVias->_ptapVias.empty()) {
        _primitives[master].push_back(p);
      } else {
        _primitivesWoTap[master].push_back(p);
      }
    }
    //logger->info("master : {0} {1} {2}", master, _primitives.size(), _primitivesWoTap.size());
    if (!_primitivesWoTap[master].empty() && _primitives[master].size() != _primitivesWoTap[master].size()) {
      for (auto wtap : {true, false}) {
        auto& t = wtap ? _primitives[master] : _primitivesWoTap[master];
        for (auto& x : t) delete x;
        t.clear();
      }
      //logger->info("removing primitive {0}", master);
      _primitives.erase(master);
      _primitivesWoTap.erase(master);
    }
  }
  //logger->info("node : {0} {1} {2}", node.name, _primitives.size(), _primitivesWoTap.size());
  if (_primitivesWoTap.empty() || _primitives.empty()) {
    //logger->info("clearing all primitves since no tapless variant found for any primitive");
    for (auto wtap : {true, false}) {
      auto& t = wtap ? _primitives : _primitivesWoTap;
      for (auto& x : t) {
        for (auto& p : x.second) delete p;
        x.second.clear();
      }
      t.clear();
    }
  }
}

TapRemoval::~TapRemoval()
{
  for (auto& x : _instances) delete x;
  _instances.clear();

  for (auto wtap : {true, false}) {
    auto& t = wtap ? _primitives : _primitivesWoTap;
    for (auto& x : t) {
      for (auto& p : x.second) delete p;
      x.second.clear();
    }
    t.clear();
  }

  delete _graph;
  _graph = nullptr;
}

long TapRemoval::deltaArea(map<string, int>* swappedIndices) const
{
  auto logger = spdlog::default_logger()->clone("PnRDB.TapRemoval.deltaArea");
  long deltaarea(0);
  if (_instances.empty()) return deltaarea;
  if (_graph == nullptr || _dist == 0) return deltaarea;
  auto nodes = _graph->dominatingSet();

  //logger->info("Found {0} nodes in dominating set {1}", nodes.size(), _dist);

  if (nodes.empty()) logger->error("No dominating nodes found");

  //for (auto& it : _instances) {
  //  deltaarea += it->primitive()->area();
  //}

  std::set<std::string> names;

  for (auto& n : nodes) {
    string name;
    auto pos = n->name().rfind("__tap_");
    if (pos != string::npos) name = n->name().substr(0, pos);
    //logger->info("{0}", n->name());
    if (!name.empty()) {
      names.insert(name);
    }
  }
  if (swappedIndices != nullptr) swappedIndices->clear();
  for (const auto& b : _instances) {
    if (names.find(b->name()) != names.end()) continue;
    if (swappedIndices != nullptr) swappedIndices->insert(make_pair(b->name(), b->index()));
    deltaarea += b->deltaArea();
  }

  //plot(_name + "_TR_" + std::to_string(deltaarea) + ".plt", swappedIndices);
  return deltaarea;
}


void TapRemoval::rebuildInstances(const PrimitiveData::PlMap& plmap)
{
  auto logger = spdlog::default_logger()->clone("PnRDB.TapRemoval.rebuildInstances");
  //for (auto& p : plmap) logger->info("plmap {0} {1} {2} {3}", p.first.first, p.second._primName, p.second._tr.origin().x(), p.second._tr.origin().y());
  
  for (auto& x : _instances) {
    delete x;
  }
  _instances.clear();
  _bbox.set();

  for (auto& it : plmap) {
    auto primIt = _primitives.find(it.second._primName);
    auto primWoTapIt = _primitivesWoTap.find(it.second._primName);
    const PrimitiveData::Primitive *prim(nullptr), *primWoTap(nullptr);
    const auto& index = it.first.second;
    if (primIt != _primitives.end() && index < primIt->second.size()) prim = primIt->second[index];
    if (primWoTapIt != _primitivesWoTap.end() && index < primWoTapIt->second.size()) primWoTap = primWoTapIt->second[index];
    //logger->info("adding {0} {1} {2} {3}", it.second._primName, index, prim ? prim->name() : "", primWoTap ? primWoTap->name() : "");
    if (prim != nullptr) {
      //logger->info("adding {0} {1}", prim->name(), primWoTap ? primWoTap->name() : "");
      auto inst = new PrimitiveData::Instance(prim, primWoTap, it.first.first, it.second._tr,
          primWoTap != nullptr ? static_cast<int>(index + primIt->second.size()) : static_cast<int>(index));
      _instances.push_back(inst);
      _instMap[it.first.first] = inst;
      //inst->print();
    }
  }
  for (auto& inst : _instances) {
    //logger->info("{0} {1}", inst->name(), inst->bbox().toString());
    _bbox.merge(inst->bbox());
  }
  //logger->info("bbox : {0}", _bbox.toString());
  delete _graph;
  _graph = new DomSetGraph::Graph;
  buildGraph(_symPairs);
}

void TapRemoval::plot(const string& pltfile, const map<string, int>* swappedIndices) const
{
  ofstream ofs(pltfile);
  if (ofs.is_open()) {
    ofs << "set title #Blocks = " << _instances.size() << " #primitives = " << _primitives.size() << "\n";
    ofs << "set nokey\n";

    // boundinf box of chip
    geom::Rect bbox;
    for (const auto& b : _instances) {
      bbox.merge(b->bbox());
    }
    ofs << "set xrange [" << bbox.xmin() - 1 << ":" << bbox.xmax() + 1 << "]\n";
    ofs << "set yrange [" << bbox.ymin() - 1 << ":" << bbox.ymax() + 1 << "]\n";

    for (const auto& b : _instances) {
      ofs << "set label \"" << b->name() << "\" at " << b->bbox().xcenter() << " , " << b->bbox().ycenter() << " center " << "\n";
      for (auto nmos : {true, false}) {
        for (const auto& t : b->getTaps(nmos)) {
          ofs << "set label \"" << (nmos ? "N" : "P") << "tap\" at " << t.xcenter() << " , " << t.ycenter() << "\n";
        }
        for (const auto& t : b->getActives(nmos)) {
          ofs << "set label \"" << (nmos ? "N" : "P") << "active\" at " << t.xcenter() << " , " << t.ycenter() << "\n";
        }
      }
    }

    // plot blocks
    ofs << "set style fill transparent pattern 5 noborder\n";
    ofs << "p[:][:] \'-\' w l ls 1, \'-\' w l ls 2, \'-\' w l ls 3";
    if (swappedIndices != nullptr) {
      ofs << ", \'-\' w filledcurves lc 0";
    }
    ofs<< "\n\n" ;
    for (const auto& b : _instances) {
      const auto& t = b->bbox();
      ofs << "\t" << t.xmin() << ' ' << t.ymin() << "\n";
      ofs << "\t" << t.xmax() << ' ' << t.ymin() << "\n";
      ofs << "\t" << t.xmax() << ' ' << t.ymax() << "\n";
      ofs << "\t" << t.xmin() << ' ' << t.ymax() << "\n";
      ofs << "\t" << t.xmin() << ' ' << t.ymin() << "\n\n";
    }
    ofs << "EOF\n\n";

    for (auto tap : {true, false}) {
      for (const auto& b : _instances) {
        for (auto nmos : {true, false}) {
          for (const auto& t : (tap ? b->getTaps(nmos) : b->getActives(nmos))) {
            ofs << "\t" << t.xmin() << ' ' << t.ymin() << "\n";
            ofs << "\t" << t.xmax() << ' ' << t.ymin() << "\n";
            ofs << "\t" << t.xmax() << ' ' << t.ymax() << "\n";
            ofs << "\t" << t.xmin() << ' ' << t.ymax() << "\n";
            ofs << "\t" << t.xmin() << ' ' << t.ymin() << "\n\n";
          }
        }
      }
      ofs << "EOF\n\n";
    }
    if (swappedIndices != nullptr) {
      for (const auto& b : _instances) {
        if (swappedIndices->find(b->name()) == swappedIndices->end()) continue;
        const auto& t = b->bbox();
        ofs << "\t" << t.xmin() << ' ' << t.ymin() << "\n";
        ofs << "\t" << t.xmax() << ' ' << t.ymin() << "\n";
        ofs << "\t" << t.xmax() << ' ' << t.ymax() << "\n";
        ofs << "\t" << t.xmin() << ' ' << t.ymax() << "\n";
        ofs << "\t" << t.xmin() << ' ' << t.ymin() << "\n\n";
      }
    }
    ofs << "EOF\n\n";


    ofs << endl << "pause -1 \'Press any key\'";
    ofs.close();
  }
}
