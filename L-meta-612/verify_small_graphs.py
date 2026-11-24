"""Check the finite case list by generating graphs one vertex at a time."""
from itertools import combinations

from small_cases import canonical, cases


def extend(n, graphs):
    result = {}
    for edges in graphs.values():
        neighbors = [sum(1 << w for edge in edges if v in edge for w in edge if v != w)
                     for v in range(n - 1)]
        for mask in range(1 << (n - 1)):
            if any((s & mask).bit_count() >= 2 for s in neighbors):
                continue
            new_edges = edges + [(v, n - 1) for v in range(n - 1) if mask & (1 << v)]
            result.setdefault(canonical(n, new_edges), new_edges)
    return result


def include(n, edges):
    neighbors = [{w for e in edges if v in e for w in e if v != w} for v in range(n)]
    if not all(neighbors) or any(neighbors.count({v}) > 1 for v in range(n)):
        return False
    return not any(all(a in cover or b in cover for a, b in edges)
                   for cover in combinations(range(n), 3))


if __name__ == "__main__":
    graphs = {(1, 0): []}
    selected = set()
    for n in range(2, 9):
        graphs = extend(n, graphs)
        selected.update(key for key, edges in graphs.items() if n >= 6 and include(n, edges))
        print(f"{n} vertices: {len(graphs) - 1} nonempty isomorphism classes", flush=True)
    expected = {canonical(n, edges) for n, _, _, edges in cases()}
    assert selected == expected
    print(f"Both constructions give the same {len(selected)} residual graphs.")
