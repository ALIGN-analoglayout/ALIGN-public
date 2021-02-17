#include <iostream>
#include <string>
#include <fstream>
#include <set>
#include <map>
#include <vector>
#include <string>
#include <sstream>
#include <cmath>
#include <cstdlib>
#include <climits>
#include <iterator>

#include <nlohmann/json.hpp>
#include <boost/filesystem.hpp>
#include <boost/geometry.hpp>
#include <boost/geometry/index/rtree.hpp>
#include <boost/function_output_iterator.hpp>

typedef std::vector<std::string> Strings;
Strings splitString(const std::string& s)
{
	Strings strs;
	std::istringstream iss(s);
	std::string tmps;
	while (iss >> tmps) {
		strs.push_back(tmps);
	}
	return move(strs);
}
namespace bg = boost::geometry;
namespace bgi = boost::geometry::index;
typedef bg::model::point<int, 2, bg::cs::cartesian> bgPt;
typedef bg::model::box<bgPt> bgBox;
typedef std::pair<bgBox, size_t> bgVal;
typedef bgi::rtree<bgVal, bgi::quadratic<8, 4> > RTree;

// Class for auto destruction
template<class T>
class AutoD {
	T& t;
	public:
	AutoD(T& argt) : t(argt) { }
	~AutoD()
	{
		for (auto& x : t) {
			delete x;
		}
		t.clear();
	}
};

template<class T>
class AutoDP {
	T& t;
	public:
	AutoDP(T& argt) : t(argt) { }
	~AutoDP()
	{
		for (auto& x : t) {
			delete x.second;
		}
		t.clear();
	}
};

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// namespace for basic geometric point and rect classes
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
namespace geom {

using namespace std;

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

		void scale(int t)
		{
			_x *= t;
			_y *= t;
		}

		void translate(int x, int y)
		{
			_x += x;
			_y += y;
		}

		void translate(int c)
		{
			_x += c;
			_y += c;
		}

		string toString() const
		{
			return to_string(_x) + "," + to_string(_y);
		}
};

class Rect
{
	private:
		int _index;
		Point _ll, _ur;

	public:
		Rect(const Point& ll, const Point& ur) : _ll(ll), _ur(ur) {}
		Rect(int x1 = INT_MAX, int y1 = INT_MAX, int x2 = -INT_MAX, int y2 = -INT_MAX, int index = -1) : _ll(x1, y1), _ur(x2, y2), _index(index)
		{
			if (x1 != INT_MAX) fix();
		}
		void set(int x1 = INT_MAX, int y1 = INT_MAX, int x2 = -INT_MAX, int y2 = -INT_MAX)
		{
			_ll.x() = x1; _ll.y() = y1; _ur.x() = x2; _ur.y() = y2;
			if (x1 != INT_MAX) fix();
		}
		void fix()
		{
			if (xmin() > xmax()) std::swap(xmin(), xmax());
			if (ymin() > ymax()) std::swap(ymin(), ymax());
		}
		const int& xmin() const { return _ll.x(); }
		const int& ymin() const { return _ll.y(); }
		const int& xmax() const { return _ur.x(); }
		const int& ymax() const { return _ur.y(); }
		int& xmin() { return _ll.x(); }
		int& ymin() { return _ll.y(); }
		int& xmax() { return _ur.x(); }
		int& ymax() { return _ur.y(); }

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

		void bloat(const int c)
		{
			_ll.translate(-c);
			_ur.translate(c);
		}

		Rect bloated(const int c)
		{
			return move(Rect(xmin() - c, ymin() - c, xmax() + c, ymax() + c));
		}
		
		int width() const { return xmax() - xmin(); }
		int height() const { return ymax() - ymin(); }

		bool isVert() const { return width() <= height(); }
		bool isHor() const { return height() <= width(); }

		void translate(const int x, const int y)
		{
			_ll.translate(x, y);
			_ur.translate(x, y);
		}

		void translate(const int c)
		{
			_ll.translate(c);
			_ur.translate(c);
		}

		Rect translate(const Point& pt) const
		{
			auto r = Rect(_ll, _ur);
			r.translate(pt.x(), pt.y());
			return move(r);
		}

		long area() const { return ((long)width()) * height(); }

		string toString() const
		{
			return _ll.toString() + " -- " + _ur.toString();
		}


};

typedef vector<Rect> Rects;

}
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// namespace for parsing and handling primitive data
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
namespace PrimitiveData {

using Rect = geom::Rect;
using Rects = geom::Rects;
using Point = geom::Point;

using namespace std;
using LayerRects = map<string, Rects>;

class Primitive
{
	private:
		int _index;
		string _name;
		Rect _bbox;
		Rects _taps, _rows;
		LayerRects _lr;

	public:
		Primitive(const string& name, const Rect& r = Rect()) :  _index(++Primitive::_globIndex), _name(name), _bbox(r)
		{
			_taps.reserve(2);
			_rows.reserve(8);
		}
		static int _globIndex;

		const string& name() const { return _name; }
		string& name() { return _name; }

		void addTap(const Rect& t) { _taps.push_back(t); }
		void addTap(const int& x1, const int& y1, const int& x2, const int& y2) { _taps.emplace_back(x1, y1, x2, y2); }
		void addRow(const Rect& r) { _rows.push_back(r); }
		void addTaps(const Rects& t) { _taps.insert(_taps.end(), t.begin(), t.end()); }
		void addRows(const Rects& r) { _rows.insert(_rows.end(), r.begin(), r.end()); }

		void addLayerRects(const string& layer, const Rect& r) { _lr[layer].push_back(r); }

		long area() const { return _bbox.area(); }
		void build();

		~Primitive()
		{
			/*cout << _name << " : " << _lr.size() << ' ' << _taps.size() << ' ' << area() << endl;
			cout << "taps : " << endl;
			for (auto& t : _taps) {
				cout << t.toString() << endl;
			}
			cout << "rows : " << endl;
			for (auto& r : _rows) {
				cout << r.toString() << endl;
			}*/
		}

		const Rects& getTaps() const { return _taps; }
		const Rects& getRows() const { return _rows; }
};
using Primitives = map<string, Primitive*>;

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
			size_t overlapRects;
			auto count = lt.query(bgi::intersects(bgBox(bgPt(val.xmin(), val.ymin()), bgPt(val.xmax(), val.ymax()))), boost::make_function_output_iterator([&overlapRects](const bgVal& val){
						overlapRects = val.second;
						}));
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
				size_t overlapRects;
				auto count = lt.query(bgi::intersects(bgBox(bgPt(r.xmin(), r.ymin()), bgPt(r.xmax(), r.ymax()))), boost::make_function_output_iterator([&overlapRects](const bgVal& val){
							overlapRects = val.second;
							}));
				if (count) {
					_rows.push_back(r);
				}
			}
		}
	}
	_lr.clear();
}

struct PlInfo {
	string _primName;
	Point _ur, _center, _ll;
};
typedef map<string, PlInfo> PlMap;

class Instance
{
	private:
		const Primitive* _prim;
		string _name;
		Point _origin;
		Rects _taps, _rows;

	public:
		Instance(const Primitive* prim, const string& name, const Point& origin);
		~Instance()
		{
			/*cout << _name << ' ' << _prim->name() << ' ' << _origin.toString() << endl;
			cout << "taps : " << endl;
			for (auto& t : _taps) {
				cout << t.toString() << endl;
			}
			cout << "rows : " << endl;
			for (auto& r : _rows) {
				cout << r.toString() << endl;
			}*/
		}

		const Primitive* primitive() const { return _prim; }

		const string& name() const { return _name; }

		const Rects& getTaps() const { return _taps; }
		const Rects& getRows() const { return _rows; }
};

typedef vector<Instance*> Instances;
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

using json = nlohmann::json;
void readPrimitivesFromJSON(Primitives& primitives, const string& pn, const string& fn)
{
	if (fn.empty()) return;
	fstream fs(fn);
	cout << "opening file : " << fn << endl;

	if (fs) {
		json j;
		fs >> j;
		//cout << j.dump();
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
}

void readJSONPrimitives(Primitives& primitives, const map<string, string>& primFiles)
{
	for (auto& it : primFiles) {
		readPrimitivesFromJSON(primitives, it.first, it.second);
		//cout << it.first << ' ' << it.second << '\n';
	}
	cout << "# Primitives : " << primitives.size() << endl;
}

void createInstances(Instances& insts, const Primitives& primitives, const PlMap& plmap)
{
	for (auto& it : plmap) {
		auto primIt = primitives.find(it.second._primName);
		cout << "# instance " << it.first << " of " << it.second._primName << endl;
		const Primitive* prim(nullptr);
		if (primIt != primitives.end()) prim = primIt->second;
		if (prim != nullptr) {
			insts.push_back(new Instance(prim, it.first, it.second._ll));
			instMap[it.first] = *insts.rbegin();
		}
	}
	cout << "# Instances : " << insts.size() << endl;
}

}

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
// namespace for classes/routines to find the dominating set of tap nodes in a graph
//////////////////////////////////////////////////////////////////////////////////////////////////////////////
namespace DomSetGraph {
using namespace std;

class Node;
class Edge;
typedef vector<Node*> Nodes;
typedef vector<const Node*> ConstNodes;
typedef map<const string, Node*> NodeMap;
typedef vector<Edge*> Edges;
typedef vector<const Edge*> ConstEdges;
typedef map<pair<const Node*, const Node*>, Edge*> EdgeMap;

enum class NodeType {
	Tap = 0,
	Active,
	MaxType
};

enum class NodeColor {
	Black = 0,
	Gray,
	White,
	MaxColor
};

class Node {
	private:
		string _name;
		NodeType _nt;
		ConstEdges _edges;
		unsigned _span;
		NodeColor _nc;

	public:
		Node(const string& name, const NodeType nt = NodeType::Tap) : _name(name), _nt(nt), _span(0), _nc(NodeColor::White) {}
		const NodeType& nodeType() const { return _nt; }
		NodeType& nodeType() { return _nt; }

		const string type() const { return (_nt == NodeType::Tap) ? "T" : "A"; }
		const string& name() const { return _name; }

		string toString() const { return name() + " " + type(); }

		void addEdge(const Edge* e) { _edges.push_back(e); }
		const ConstEdges& edges() const { return _edges; }

		void setSpan(const unsigned n) { _span = n; }
		unsigned span() const { return _span; }

		void setColor(const NodeColor& nc) { _nc = nc; }
		const NodeColor& nodeColor() const { return _nc; }
};

class Edge {
	private:
		const Node *_u, *_v;
		string _name;
	
	public:
		Edge(const Node* n1, const Node* n2, const string& name) : _u(n1), _v(n2), _name(name) {}
		const string& name() const { return _name; }
		const Node* u() const { return _u; }
		const Node* v() const { return _v; }
		string toString() const { return _u->name() + " " + _v->name() + " " + name(); }
};

class Graph {
	private:
		Nodes _nodes;
		NodeMap _nodeMap;
		Edges _edges;
		EdgeMap _edgeMap;

	public:
		Graph();
		~Graph();

		void addNode(const string& name, const NodeType& nt);
		void addEdge(const string& u, const string& v, const string& name = "");

		const Edge* findEdge(const string& u, const string& v) const;

		void parseGraph(const string& fn);
		void print() const;

		ConstNodes dominatingSet() const;

		const Nodes& nodes() const { return _nodes; }
		const Edges& edges() const { return _edges; }

};

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
	cout << "# Graph " << endl;
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
	}
}

void Graph::parseGraph(const string& fn)
{
	ifstream ifs(fn);
	if (!ifs) return;

	cout << "Parsing graph from file : " << fn << endl << endl;

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
	set<const Node*> whiteNodes, dom;
	for (auto& n : _nodes) {
		whiteNodes.insert(n);
		n->setColor(NodeColor::White);
	}

	while (!whiteNodes.empty()) {
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

	ConstNodes domNodes;
	for (auto& n : dom) domNodes.push_back(n);

	return move(domNodes);
}

}
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

using namespace std;
string parseArg(int argc, char* argv[], const string& argName, const string& defl = "")
{
	string s(defl);
	for (unsigned i = 1; i < argc; ++i) {
		if (argName == argv[i] && (i + 1) < argc) {
			s = argv[i + 1];
			break;
		}
	}
	return s;
}

namespace boostfs = boost::filesystem;

void readPrimitives(PrimitiveData::Primitives& primitives, const string& pdir)
{
	map<string, string> primFiles;
	boostfs::path p(pdir);
	try {
		if (boostfs::exists(p) && boostfs::is_directory(p)) {
			for (auto&& x : boostfs::directory_iterator(p)) {
				string str = x.path().filename().string(); 
				auto ind = str.find(".json");
				if (str.find(".json") != string::npos && str.find(".debug.json") == string::npos && str.find(".gds.json") == string::npos) {
					primFiles[str.substr(0, ind)] = pdir + "/" + str;
				}
			}
		}
	} catch (const boostfs::filesystem_error& ex) {
		cout << ex.what() << '\n';
	}
	PrimitiveData::readJSONPrimitives(primitives, primFiles);
}

void createInstances(PrimitiveData::Instances& instances, const PrimitiveData::Primitives& primitives, const string& plfile)
{
	PrimitiveData::PlMap plmap;
	ifstream ifs(plfile);
	string line;
	while (!ifs.eof()) {
		getline(ifs, line);
		Strings strs = splitString(line);
		if (!strs.empty()) {
            if (strs[1].find("PMOS") == string::npos && primitives.find(strs[1]) != primitives.end() && strs.size() >= 4) {
                plmap[strs[0]]._primName = strs[1];
				plmap[strs[0]]._ll = geom::Point(stoi(strs[2])*5, stoi(strs[3])*5);
			}
		}
	}
	PrimitiveData::createInstances(instances, primitives, plmap);
}

void buildGraph(DomSetGraph::Graph& graph, const PrimitiveData::Instances& insts, const unsigned dist)
{
	RTree rtree;
	map<string, geom::Rect> allTaps;
	for (auto& inst : insts) {
		auto& taps = inst->getTaps();
		for (unsigned i = 0; i < taps.size(); ++i) {
			bgBox b(bgPt(taps[i].xmin(), taps[i].ymin()), bgPt(taps[i].xmax(), taps[i].ymax()));
			rtree.insert(bgVal(b, graph.nodes().size()));
			string nodeName(inst->name() + "__tap_" + to_string(i));
			allTaps[nodeName] = taps[i];
			graph.addNode(nodeName, DomSetGraph::NodeType::Tap);
		}
		auto& rows = inst->getRows();
		for (unsigned i = 0; i < rows.size(); ++i) {
			bgBox b(bgPt(rows[i].xmin(), rows[i].ymin()), bgPt(rows[i].xmax(), rows[i].ymax()));
			rtree.insert(bgVal(b, graph.nodes().size()));
			graph.addNode(inst->name() + "__row_" + to_string(i), DomSetGraph::NodeType::Active);
		}
	}

	cout << allTaps.size() << endl;

	for (auto& it : allTaps) {
		auto r = it.second.bloated(dist);
		bgBox box(bgPt(r.xmin(), r.ymin()), bgPt(r.xmax(), r.ymax()));
		vector<bgVal> overlapRects;
		rtree.query(bgi::covered_by(box), back_inserter(overlapRects));
		for (auto& val : overlapRects) {
			auto& rname = graph.nodes()[val.second]->name();
			if (it.first != rname) {
				//cout << it.first << ' ' << rname << endl;
				graph.addEdge(it.first, rname);
			}
		}
	}

}

long deltaArea(const string& pdir, const string& pdirWOTap, const string& plfile, const unsigned dist)
{
	PrimitiveData::Primitives primitives, primitivesWOTap;
	PrimitiveData::Instances instances;
	AutoDP<PrimitiveData::Primitives> tp(primitives);
	AutoDP<PrimitiveData::Primitives> tpWO(primitivesWOTap);
	AutoD<PrimitiveData::Instances> ti(instances);

	readPrimitives(primitives, pdir);
	if (!pdirWOTap.empty()) readPrimitives(primitivesWOTap, pdirWOTap);
	createInstances(instances, primitives, plfile);

	DomSetGraph::Graph graph;
	buildGraph(graph, instances, dist);
	
	auto nodes = graph.dominatingSet();

	long deltaarea(0);
	for (auto& it : instances) {
		deltaarea += it->primitive()->area();
	}

	for (auto& n : nodes) {
		cout << "dom : " << n->name() << endl;
		string name;
		auto pos = n->name().rfind("__tap_");
		if (pos != string::npos) name = n->name().substr(0, pos);
		if (!name.empty()) {
			auto it = PrimitiveData::instMap.find(name);
			if (it != PrimitiveData::instMap.end()) {
				auto itWO = primitivesWOTap.find(it->second->primitive()->name());
				if (itWO != primitivesWOTap.end()) {
					auto delarea = it->second->primitive()->area() - itWO->second->area();
					cout << "delta area : " << delarea << endl;
					deltaarea += delarea;
				}
			}
		}
	}
	return deltaarea;
}

int main(int argc, char* argv[])
{
	string pdir = parseArg(argc, argv, "-primitive_dir");
	string pdirWOTap = parseArg(argc, argv, "-primitive_dir_wo_tap");
	string plfile = parseArg(argc, argv, "-placement_file");
	string dist = parseArg(argc, argv, "-distance", "25000");

	if (!pdir.empty() && !pdirWOTap.empty() && !plfile.empty() && !dist.empty()) {
		cout << deltaArea(pdir, pdirWOTap, plfile, stoi(dist)) << endl;
	}
	return 0;
}
