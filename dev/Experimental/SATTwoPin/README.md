# SAT-based Two-Pin Single Layer Router


To run:
```
pip install python-sat

cd ../Pysat/tally
pip install -e .
cd -

python main.py
```

# Lee Router with random net ordering

There is also a simple breadth-first router that uses a random net ordering.
You can run it using:
```
python lee.py
```
There are three options:
```
-n <int> for number of random permutations
-a (bfs|astar|dijkstra) for the algorithm
-m (two_nets_10x10|ten_nets_8x8|ten_nets_16x16|ten_nets_24x24|river_8x8)
```

The `bfs` algoritm uses unit cost for each horizontal or vertical step with no extra cost for changing direction. The `astar` and `dijkstra` algorithm include a 10 unit penalty for changing direction (corresponding to a via).
