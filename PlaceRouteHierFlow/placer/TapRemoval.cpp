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

void Primitive::build()
{
  map<string, RTree> layerTree;
  for (auto& idx : _lr) {
    auto& tr = layerTree[idx.first];
    for (unsigned i = 0; i < idx.second.size(); ++i) {
      bgBox b(bgPt(idx.second[i].xmin(), idx.second[i].ymin()), bgPt(idx.second[i].xmax(), idx.second[i].ymax()));
      tr.insert(bgVal(b, i));
    }
  }
  map<pair<int, int>, Rect> verMap, horMap;
  for (auto& t : _taps) {
    verMap[make_pair(t.ymin(), t.ymax())].merge(t);
    horMap[make_pair(t.xmin(), t.xmax())].merge(t);
  }
  bool verTap(true);
  for (auto& idx : verMap) {
    auto& val = idx.second;
    if (layerTree.find("Poly") != layerTree.end()) {
      auto& lt = layerTree["Poly"];
      vector<bgVal> overlapRects;
      auto count = lt.query(bgi::intersects(bgBox(bgPt(val.xmin(), val.ymin()), bgPt(val.xmax(), val.ymax()))) 
          && bgi::satisfies([&overlapRects](bgVal const& v) { return overlapRects.empty(); }),
          back_inserter(overlapRects));
      if (count) {
        verTap = false;
        break;
      }
    }
  }
  _taps.clear();
  for (auto& idx : verTap ? verMap : horMap) {
    _taps.push_back(idx.second);
  }
  if (_lr.find("Active") != _lr.end()) {
    for (auto& r : _lr["Active"]) {
      if (layerTree.find("Poly") != layerTree.end()) {
        auto& lt = layerTree["Poly"];
        vector<bgVal> overlapRects;
        auto count = lt.query(bgi::intersects(bgBox(bgPt(r.xmin(), r.ymin()), bgPt(r.xmax(), r.ymax())))
            && bgi::satisfies([&overlapRects](bgVal const& v) { return overlapRects.empty(); }),
            back_inserter(overlapRects));
        if (count) {
          _actives.push_back(r);
        }
      }
    }
  }
  _lr.clear();
}


Instance::Instance(const Primitive* prim, const Primitive* primWoTap, const string& name, const Transform& tr, const int& ind) :
_prim(prim), _primWoTap(primWoTap), _name(name), _bbox(Rect()), _woTapIndex(ind)
{
  if (_prim) {
    for (const auto& t : _prim->getTaps()) {
      _taps.push_back(t.transform(tr, _prim->width(), _prim->height()));
    }
    for (const auto& r : _prim->getActives()) {
      _actives.push_back(r.transform(tr, _prim->width(), _prim->height()));
    }
    _bbox = _prim->bbox().transform(tr, _prim->width(), _prim->height());
  }
}

void Instance::print() const
{
  auto logger = spdlog::default_logger()->clone("placer.Instance.print");
  logger->info("{0} {1} {2}", _name, _prim->name(), _primWoTap->name());
  logger->info("taps : ");
  for (auto& t : _taps) {
    logger->info("{0}", t.toString());
  }
  logger->info("actives : ");
  for (auto& r : _actives) {
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

void Graph::addNode(const string& name, const NodeType& nt, const long& da, const bool isb)
{
  if (_nodeMap.find(name) != _nodeMap.end()) return;
  Node *n = new Node(name, nt, da);
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

void Graph::parseGraph(const string& fn)
{
  ifstream ifs(fn);
  if (!ifs) return;

  //cout << "Parsing graph from file : " << fn << endl << endl;

  string line;
  while (!ifs.eof()) {
    getline(ifs, line);
    Strings strs = splitString(line);
    if (!strs.empty()) {
      if (strs[0][0] == '#') continue;
      if (strs[0] == "Node" && strs.size() >= 2) {
        NodeType nt = (strs.size() >= 3) ? (strs[2] == "T" ? NodeType::Tap : NodeType::Active) : NodeType::Tap;
        addNode(strs[1], nt);
      } else if (strs[0] == "Edge" && strs.size() >= 3) {
        addEdge(strs[1], strs[2], strs.size() > 3 ? strs[3] : "");
      }
    }
  }

  ifs.close();
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
    //  logger->info("edge : {0} {1} {2}", e->name(), e->u()->name(), e->v()->name());
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
      }
    }

    for (auto& n : maxNbrWhites) {
      if (NodeColor::White == n->nodeColor()) dom.insert(n);
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
}

void TapRemoval::buildGraph()
{
  RTree rtree;
  map<string, geom::Rect> allTaps;
  if (_graph == nullptr) _graph = new DomSetGraph::Graph;
  for (const auto& inst : _instances) {
    auto& taps = inst->getTaps();
    for (unsigned i = 0; i < taps.size(); ++i) {
      bgBox b(bgPt(taps[i].xmin(), taps[i].ymin()), bgPt(taps[i].xmax(), taps[i].ymax()));
      rtree.insert(bgVal(b, _graph->nodes().size()));
      string nodeName(inst->name() + "__tap_" + to_string(i));
      allTaps[nodeName] = taps[i];
      _graph->addNode(nodeName, DomSetGraph::NodeType::Tap, inst->deltaArea(), inst->isBlack());
    }
    auto& actives = inst->getActives();
    for (unsigned i = 0; i < actives.size(); ++i) {
      bgBox b(bgPt(actives[i].xmin(), actives[i].ymin()), bgPt(actives[i].xmax(), actives[i].ymax()));
      rtree.insert(bgVal(b, _graph->nodes().size()));
      _graph->addNode(inst->name() + "__active_" + to_string(i), DomSetGraph::NodeType::Active, inst->deltaArea());
    }
  }

  //cout << allTaps.size() << endl;

  for (auto& it : allTaps) {
    auto r = it.second.bloated(_dist);
    bgBox box(bgPt(r.xmin(), r.ymin()), bgPt(r.xmax(), r.ymax()));
    vector<bgVal> overlapRects;
    rtree.query(bgi::covered_by(box), back_inserter(overlapRects));
    for (auto& val : overlapRects) {
      auto& rname = _graph->nodes()[val.second]->name();
      if (it.first != rname) {
        //cout << it.first << ' ' << rname << endl;
        _graph->addEdge(it.first, rname);
      }
    }
  }

}

TapRemoval::TapRemoval(const PnRDB::hierNode& node, const unsigned dist) : _dist(dist), _name(node.name), _graph(nullptr)
{
  auto logger = spdlog::default_logger()->clone("placer.TapRemoval.TapRemoval");
  for (unsigned i = 0; i < node.Blocks.size(); ++i) {
    if (node.Blocks[i].instance.empty()) continue;
    const auto& master=node.Blocks[i].instance.back().master;
    for (unsigned j = 0; j < node.Blocks[i].instance.size(); ++j) {
      const auto& n = node.Blocks[i].instance[j];
      PrimitiveData::Primitive *p(nullptr);
      p = new PrimitiveData::Primitive(master, geom::Rect(node.Blocks[i].instance[j].originBox));

      for (const auto& t : n._tapVias) p->addTap(geom::Rect(t));
      for (const auto& t : n._activeVias) p->addActive(geom::Rect(t));

      if (!n._tapVias.empty()) {
        _primitives[master].push_back(p);
      } else {
        _primitivesWoTap[master].push_back(p);
      }
    }
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
//  auto logger = spdlog::default_logger()->clone("PnRDB.TapRemoval.rebuildInstances");
//  for (auto& p : plmap) {
//    logger->info("plmap {0} {1} {2} {3}", p.first, p.second._primName, p.second._ll.x(), p.second._ll.y());
//  }
  
  for (auto& x : _instances) {
    delete x;
  }
  _instances.clear();

  for (auto& it : plmap) {
    auto primIt = _primitives.find(it.second._primName);
    auto primWoTapIt = _primitivesWoTap.find(it.second._primName);
    const PrimitiveData::Primitive *prim(nullptr), *primWoTap(nullptr);
    const auto& index = it.first.second;
    if (primIt != _primitives.end() && index < primIt->second.size()) prim = primIt->second[index];
    if (primWoTapIt != _primitivesWoTap.end() && index < primWoTapIt->second.size()) primWoTap = primWoTapIt->second[index];
    if (prim != nullptr && (_primitivesWoTap.empty() || primWoTap != nullptr)) {
      auto inst = new PrimitiveData::Instance(prim, primWoTap, it.first.first, it.second._tr, static_cast<int>(index + primIt->second.size()));
      _instances.push_back(inst);
      _instMap[it.first.first] = inst;
      //inst->print();
    }
  }
  delete _graph;
  _graph = new DomSetGraph::Graph;
  buildGraph();
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
      for (const auto& t : b->getTaps()) {
        ofs << "set label \"tap\" at " << t.xcenter() << " , " << t.ycenter() << "\n";
      }
      for (const auto& t : b->getActives()) {
        ofs << "set label \"active\" at " << t.xcenter() << " , " << t.ycenter() << "\n";
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
        for (const auto& t : (tap ? b->getTaps() : b->getActives())) {
          ofs << "\t" << t.xmin() << ' ' << t.ymin() << "\n";
          ofs << "\t" << t.xmax() << ' ' << t.ymin() << "\n";
          ofs << "\t" << t.xmax() << ' ' << t.ymax() << "\n";
          ofs << "\t" << t.xmin() << ' ' << t.ymax() << "\n";
          ofs << "\t" << t.xmin() << ' ' << t.ymin() << "\n\n";
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
