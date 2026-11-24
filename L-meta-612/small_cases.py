"""Emit C4-free reduced cases of cover number four or five on at most eight vertices."""
from itertools import combinations, permutations, product

from cover_kernels import kernels


def canonical(n, edges):
    neighbors = [{w for e in edges if v in e for w in e if w != v} for v in range(n)]
    colors = [len(ns) for ns in neighbors]
    while True:
        profiles = [(colors[v], tuple(sorted(colors[w] for w in neighbors[v]))) for v in range(n)]
        palette = {p: i for i, p in enumerate(sorted(set(profiles)))}
        refined = [palette[p] for p in profiles]
        if len(set(refined)) == len(set(colors)):
            colors = refined
            break
        colors = refined
    blocks = [[v for v in range(n) if colors[v] == t] for t in sorted(set(colors))]
    best = None
    pairs = list(combinations(range(n), 2))
    for order in product(*(permutations(block) for block in blocks)):
        labels = tuple(v for block in order for v in block)
        bits = sum(1 << j for j, (a, b) in enumerate(pairs) if labels[b] in neighbors[labels[a]])
        best = bits if best is None else min(best, bits)
    return n, best


def cases():
    result = {}
    for cover in (4, 5):
        for n, m, edges in kernels(cover, max_vertices=8):
            result.setdefault(canonical(n, edges), (n, m, cover, edges))
    return sorted(result.values())


if __name__ == "__main__":
    for i, (n, m, cover, edges) in enumerate(cases()):
        print(i, n, m, cover, *(v for edge in edges for v in edge))
