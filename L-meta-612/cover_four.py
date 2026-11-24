"""Emit the residual cover-four graphs after the three leaf reductions."""
from itertools import combinations

from cover_kernels import kernels
from small_cases import canonical


def removable(n, edges, cover):
    neighbors = [{w for e in edges if v in e for w in e if v != w} for v in range(n)]
    for b in range(n):
        if len(neighbors[b]) != 1:
            continue
        a = next(iter(neighbors[b]))
        if len(neighbors[a]) <= 2:
            return True
        surviving = [edge for edge in edges if b not in edge]
        smaller = combinations([v for v in range(n) if v != b], cover - 1)
        if not any(all(u in s or v in s for u, v in surviving) for s in smaller):
            return True
    return False


def cases():
    result = {}
    for n, m, edges in kernels(4):
        if not removable(n, edges, 4):
            result.setdefault(canonical(n, edges), (n, m, 4, edges))
    return sorted(result.values())


if __name__ == "__main__":
    for i, (n, m, cover, edges) in enumerate(cases()):
        print(i, n, m, cover, *(v for edge in edges for v in edge))
