#ifndef TAPREMOVAL_H_
#include <string>
#include <map>
#include <vector>
#include <string>
#include <climits>

#include "../PnRDB/datatype.h"

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
		void scale(int t) { _x *= t; _y *= t; }
		void translate(int x, int y) { _x += x; _y += y; }
		void translate(int c) { _x += c; _y += c; }
		string toString() const { return to_string(_x) + "," + to_string(_y); }
};

class Rect
{
	private:
		Point _ll, _ur;
		int _index;

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

		void bloat(const int c) { _ll.translate(-c); _ur.translate(c); }
		Rect bloated(const int c) { return move(Rect(xmin() - c, ymin() - c, xmax() + c, ymax() + c)); }
		
		int width() const { return xmax() - xmin(); }
		int height() const { return ymax() - ymin(); }

		bool isVert() const { return width() <= height(); }
		bool isHor() const { return height() <= width(); }

		void translate(const int x, const int y) { _ll.translate(x, y); _ur.translate(x, y); }
		void translate(const int c) { _ll.translate(c); _ur.translate(c); }

		Rect translate(const Point& pt) const
		{
			auto r = Rect(_ll, _ur);
			r.translate(pt.x(), pt.y());
			return move(r);
		}

		long area() const { return ((long)width()) * height(); }
		string toString() const { return _ll.toString() + " -- " + _ur.toString(); }


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

struct PlInfo {
	string _primName;
	Point _ll;
	unsigned _hflip : 1;
	unsigned _vflip : 1;
	PlInfo(const string& name, const geom::Point& ll, int hf, int vf) :
		_primName(name), _ll(ll),
		_hflip(hf == 0 ? 0 : 1), _vflip(vf == 0 ? 0 : 1) {}
};
typedef map<pair<string, unsigned>, PlInfo> PlMap;

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

}

class TapRemoval {
	private:
		unsigned _dist;
		DomSetGraph::Graph *_graph;
		PrimitiveData::Instances _instances;
		PrimitiveData::Primitives _primitives, _primitivesWOTap;

		void buildGraph();
	public:
		TapRemoval(const PnRDB::hierNode& node, const unsigned dist);
		~TapRemoval();
		void readPrimitives(PrimitiveData::Primitives& primitives, const string& pdir);
		//void createInstances(const PrimitiveData::PlMap& plmap);
		long deltaArea() const;
		void rebuildInstances(const PrimitiveData::PlMap& plmap);
		bool containsPrimitive(const string& prim) const { return _primitives.find(prim) != _primitives.end(); }

};
//////////////////////////////////////////////////////////////////////////////////////////////////////////////

#endif
