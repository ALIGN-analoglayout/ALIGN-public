# Experiment with SAT-based Subgraph Isomorphism (monomorphism)

First build the `tally` image in `Pysat/`

```bash
docker build -t sgi .

docker run --rm -it sgi bash -c "source /sympy/bin/activate && cd /scripts && pytest -- sat_based_sgi.py"
```

## Encoding for Monomorphism
As far as I understand it, the graph monomorphism identification problem is to find a mapping p for the vertices in graph G'=(V',E') to the vertices in another graph G=(V,E) such that for every edge {u',v'} in E', the edge {p(u'),p(v')} is in E.
This is easy to represent in SAT.
You first represent the mapping.
You can do this by setting up a matrix of boolean variables:
```
00
10
01
```
A one in a particular i,j position means that vertex j (column) in G' maps to vertex i (row) in G.
In each row, at most one element can be one. In each column exactly one element must be one.
For this to be possible, the number of columns must be no greater than the number of rows. 
There are standard encodings for these constraints (`emit_at_most_one` and `emit_exactly_one` in `tally.Tally`.)

To complete the encoding, we need to show, for each edge in E', that the mapped vertices form an edge in E.
We can do this by adding a clause for each edge in E' that says that the mapped version of this edge is the same as at least one of the edges in E.
```
for each e'=(u',v') in E'
   OR_[(u,v) in E] (p(u,u') AND p(v,v') OR p(v,u') AND p(u,v'))
```
We need to introduce 2*|E|*|E'| new SAT variables to encode the AND terms.

## Encoding for Subgraph Isomorphism
The subgraph isomorphism problem is somewhat different. We still need a mapping, but every edge incident on the edges to mapped vertices must also be present in the subgraph (E'). So how about this encoding:
```bash
isMapped(i) = OR_j p(i,j)
for each e=(u,v) in E
    ~isMapped(u) OR ~isMapped(v) OR OR_[(u',v') in E'] (p(u,u') AND p(v,v') OR p(v,u') AND p(u,v'))
```
The loops are done the other way around. There is a clause for each edge in the big graph and the size of each clause is related to the number of edges in the small graph. Again, there are 2*|E|*|E'| new SAT variables for the AND terms plus |E| more to encode the isMapped values.

## Possible Improvements
We can simplify the encoding if the graph is bipartite. The matrix of boolean variables can be split into four blocks, with only zeroes in the top right and lower left blocks. Also, we don't need to test both possible edge directions (u,v) and (v,u). We know edges are between two distinct sets of vertices (i.e., it is bipartite), so even through the graph is undirected, we only need to make one test.

If we know particular vertices match (like ground or vdd), then we can enforce that by setting the corresponding boolean variable in the matrix.
If there are edge or vertex attributes that much match, we can add that to the encoding, restricting the possible solutions.
