"""Independently check the graph facts used in ExcludeTen.md."""
from itertools import combinations

EDGES = {
    (0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3),
    (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7),
}
VERTICES = range(8)
def edge(i, j):
    return (min(i,j), max(i,j)) in EDGES

for i, j in combinations(VERTICES, 2):
    assert edge(i,j) == ((i ^ j) in (1, 2, 4))
    assert any(k not in (i,j) and edge(i,k) and not edge(j,k) for k in VERTICES)

for v in VERTICES:
    w = v ^ 7
    vertices = set(VERTICES) - {v,w}
    assert any(edge(w,k) for k in vertices)
    order = [v ^ u for u in (1, 3, 2, 6, 4, 5)]
    cycle = {tuple(sorted((order[i],order[(i+1)%6]))) for i in range(6)}
    assert cycle == {e for e in EDGES if set(e) <= vertices}

print("Verified 28 distinguishing vertex pairs and all 8 ordered antipodal deletions.")
