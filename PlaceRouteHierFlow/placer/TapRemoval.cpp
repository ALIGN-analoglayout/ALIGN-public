#include "TapRemoval.h"
#include <set>
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

namespace PrimitiveData {

int Primitive::_globIndex = -1;

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
					_rows.push_back(r);
				}
			}
		}
	}
	_lr.clear();
}

typedef map<string, Instance*> InstanceMap;
InstanceMap instMap;

Instance::Instance(const Primitive* prim, const string& name, const Point& origin) :
_prim(prim), _name(name), _origin(origin)
{
	if (_prim) {
		for (const auto& t : _prim->getTaps()) {
			_taps.push_back(t.translate(_origin));
		}
		for (const auto& r : _prim->getRows()) {
			_rows.push_back(r.translate(_origin));
		}
	}
}

//using json = nlohmann::json;
void readPrimitivesFromJSON(Primitives& primitives, const string& pn, const string& fn)
{
/*
	if (fn.empty()) return;
	ifstream fs(fn);

	if (fs) {
		json j;
		fs >> j;
		Rect bbox;
		if (j.find("bbox") != j.end()) {
			auto& b = j["bbox"];
			bbox.set(b[0], b[1], b[2], b[3]);
		}
		Primitive *p(nullptr);
		if (primitives.find(pn) == primitives.end()) {
			p = new Primitive(pn, bbox);
			primitives[pn] = p;
			if (j.find("terminals") != j.end()) {
				json& arr = j["terminals"];
				for (auto it = arr.begin(); it != arr.end(); ++it) {
					auto& t = *it;
					string layer = t["layer"];
					if (t.find("rect") != t.end()) {
						auto& r = t["rect"];
						if (t["pin"] == "B") {
							p->addTap(r[0], r[1], r[2], r[3]);
						}
						p->addLayerRects(layer, Rect(r[0], r[1], r[2], r[3]));
					}
				}
			}
			p->build();
		}
	}
*/
}

void readJSONPrimitives(Primitives& primitives, const map<string, string>& primFiles)
{
	for (auto& it : primFiles) {
		readPrimitivesFromJSON(primitives, it.first, it.second);
	}
	//cout << "# Primitives : " << primitives.size() << endl;
}

void createInstances(Instances& insts, const Primitives& primitives, const PlMap& plmap)
{
	for (auto& it : plmap) {
		auto primIt = primitives.find(it.second._primName);
		//cout << "# instance " << it.first << " of " << it.second._primName << endl;
		const Primitive* prim(nullptr);
		if (primIt != primitives.end()) prim = primIt->second;
		if (prim != nullptr) {
			insts.push_back(new Instance(prim, it.first, it.second._ll));
			instMap[it.first] = *insts.rbegin();
		}
	}
	//cout << "# Instances : " << insts.size() << endl;
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

void Graph::addNode(const string& name, const NodeType& nt)
{
	if (_nodeMap.find(name) != _nodeMap.end()) return;
	Node *n = new Node(name, nt);
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

ConstNodes Graph::dominatingSet() const
{
	//auto logger = spdlog::default_logger()->clone("PnRDB.TapRemoval.dominatingSet");
	set<const Node*> whiteNodes, dom;
	size_t tapNodes(0), rowNodes(0), isoRow(0);
	ConstNodes domNodes;
	for (auto& n : _nodes) {
		bool foundTap(false);
		if (n->nodeType() == NodeType::Tap) {
			foundTap = true;
			++tapNodes;
		} else {
			++rowNodes;
			for (auto& e : n->edges()) {
				const Node* nbr = (e->v() == n) ? e->u() : e->v();
				if (nbr && nbr->nodeType() == NodeType::Tap) {
					foundTap = true;
					break;
				}
			}
		}
		if (foundTap) {
			whiteNodes.insert(n);
			n->setColor(NodeColor::White);
		} else ++isoRow;
	}
	//logger->info("tap nodes : {0} row nodes : {1} {2}", tapNodes, rowNodes, isoRow); 
	

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
		Nodes maxNbrWhites;
		unsigned maxW(0);
		for (auto& n : _nodes) {
			if (n->nodeType() != NodeType::Tap) continue;
			if (maxW < n->span()) {
				maxNbrWhites.clear();
				maxNbrWhites.push_back(n);
				maxW = n->span();
			} else if (maxW == n->span()) {
				maxNbrWhites.push_back(n);
			}
		}

		for (auto& n : maxNbrWhites) {
			n->setColor(NodeColor::Black);
			for (auto& e : n->edges()) {
				const Node* nbr = (e->v() == n) ? e->u() : e->v();
				if (nbr->nodeColor() != NodeColor::Black) {
					const_cast<Node*>(nbr)->setColor(NodeColor::Gray);
				}
			}
			dom.insert(n);
		}

		for (auto& n : _nodes) {
			if (n->nodeColor() != NodeColor::White) whiteNodes.erase(n);
		}
	}

	for (auto& n : dom) domNodes.push_back(n);

	return move(domNodes);
}

}

void TapRemoval::readPrimitives(PrimitiveData::Primitives& primitives, const string& pdir)
{
	map<string, string> primFiles;
	if (!primFiles.empty()) PrimitiveData::readJSONPrimitives(primitives, primFiles);
}

void TapRemoval::createInstances(const ILP_solver& solver, PnRDB::hierNode &node)
{
	//auto logger = spdlog::default_logger()->clone("PnRDB.TapRemoval.createInstances");
	if (_primitives.empty()) return;
	PrimitiveData::PlMap plmap;
	for (unsigned i = 0; i < node.Blocks.size(); ++i) {
		//logger->info("print : {0} {1}", node.Blocks[i].instance.size(), node.Blocks[i].selectedInstance);
		auto& index = node.Blocks[i].selectedInstance;
		if (index >= node.Blocks[i].instance.size()) continue;
		auto& block = node.Blocks[i].instance[index];
		if (block.master.find("PMOS") == string::npos && _primitives.find(block.master) != _primitives.end()) {
			plmap.insert(std::make_pair(block.name, PlInfo(block.master,
							geom::Point(block.placedBox.LL.x, block.placedBox.LL.y), 
							index, solver.Blocks[i].H_flip, solver.Blocks[i].V_flip)));
		}
	}
	PrimitiveData::createInstances(_instances, _primitives, plmap);
}

void TapRemoval::buildGraph(const unsigned dist)
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
			_graph->addNode(nodeName, DomSetGraph::NodeType::Tap);
		}
		auto& rows = inst->getRows();
		for (unsigned i = 0; i < rows.size(); ++i) {
			bgBox b(bgPt(rows[i].xmin(), rows[i].ymin()), bgPt(rows[i].xmax(), rows[i].ymax()));
			rtree.insert(bgVal(b, _graph->nodes().size()));
			_graph->addNode(inst->name() + "__row_" + to_string(i), DomSetGraph::NodeType::Active);
		}
	}

	//cout << allTaps.size() << endl;

	for (auto& it : allTaps) {
		auto r = it.second.bloated(dist);
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

TapRemoval::TapRemoval(const PnRDB::hierNode& node)
{
}

TapRemoval::~TapRemoval()
{
	for (auto& x : _instances) delete x;
	_instances.clear();

	for (auto wtap : {true, false}) {
		auto& t = wtap ? _primitives : _primitivesWOTap;
		for (auto& x : t) delete x.second;
		t.clear();
	}

	delete _graph;
	_graph = nullptr;
}

long TapRemoval::deltaArea() const
{
	//auto logger = spdlog::default_logger()->clone("PnRDB.TapRemoval.deltaArea");
	long deltaarea(0);
	if (_graph == nullptr) return deltaarea;
	auto nodes = _graph->dominatingSet();

	//logger->info("Found {0} nodes in dominating set", nodes.size());

	//for (auto& it : _instances) {
	//	deltaarea += it->primitive()->area();
	//}

	for (auto& n : nodes) {
		string name;
		auto pos = n->name().rfind("__tap_");
		if (pos != string::npos) name = n->name().substr(0, pos);
		if (!name.empty()) {
			auto it = PrimitiveData::instMap.find(name);
			if (it != PrimitiveData::instMap.end()) {
				auto itWO = _primitivesWOTap.find(it->second->primitive()->name());
				//logger->info("Remove tap for cell {0}", it->second->name());
				if (itWO != _primitivesWOTap.end()) {
					auto delarea = it->second->primitive()->area() - itWO->second->area();
					deltaarea += delarea;
				}
			}
		}
	}
	return deltaarea;
}


void TapRemoval::rebuildInstances(const PrimitiveData::PlMap& plmap) {
//	auto logger = spdlog::default_logger()->clone("PnRDB.TapRemoval.rebuildInstances");
//
//	for (auto& p : plmap) {
//		logger->info("plmap {0} {1} {2} {3}", p.first, p.second._primName, p.second._ll.x(), p.second._ll.y());
//	}
	
	for (auto& x : _instances) {
		delete x;
	}
	_instances.clear();

	PrimitiveData::createInstances(_instances, _primitives, plmap);
	delete _graph;
	_graph = new DomSetGraph::Graph;

	buildGraph(_dist);

}
