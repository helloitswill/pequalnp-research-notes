"""Generate square-free kernels with a distinguished minimum cover and no duplicate leaves."""
import argparse
from itertools import combinations, permutations


def kernels(cover=3, max_vertices=None):
    pairs = list(combinations(range(cover), 2))
    pair_index = {p: i for i, p in enumerate(pairs)}
    universe = range(1 << cover)
    larger = [s for s in universe if s.bit_count() >= 2]
    contained_pairs = {s: sum(1 << i for i, (a, b) in enumerate(pairs) if s >> a & s >> b & 1) for s in larger}
    permutations_of_cover = list(permutations(range(cover)))
    relabel = [[sum(1 << p[v] for v in range(cover) if s >> v & 1) for s in universe]
               for p in permutations_of_cover]
    result = {}
    for internal in range(1 << len(pairs)):
        inside = [e for i, e in enumerate(pairs) if internal & (1 << i)]
        neighbors = [sum(1 << w for e in inside if v in e for w in e if w != v) for v in range(cover)]
        if any((neighbors[a] & neighbors[b]).bit_count() > 1 for a, b in pairs):
            continue
        images = [sum(1 << pair_index[tuple(sorted((p[a], p[b])))] for a, b in inside)
                  for p in permutations_of_cover]
        if min(images) != internal:
            continue
        symmetries = [r for image, r in zip(images, relabel) if image == internal]
        used = sum(1 << i for i, (a, b) in enumerate(pairs) if neighbors[a] & neighbors[b])
        choices = [((), used)]
        for s in larger:
            choices += [(chosen + (s,), taken | contained_pairs[s]) for chosen, taken in choices
                        if not (taken & contained_pairs[s])]
        internal_covers = [s for s in universe if all((s >> a | s >> b) & 1 for a, b in inside)]
        for chosen, _ in choices:
            for singletons in universe:
                types = tuple(sorted((*chosen, *(1 << v for v in range(cover) if singletons >> v & 1))))
                n = cover + len(types)
                if n <= 5 or (max_vertices is not None and n > max_vertices):
                    continue
                if any(tuple(sorted(r[s] for s in types)) < types for r in symmetries):
                    continue
                minimum = min(s.bit_count() + sum(bool(t & ~s) for t in types) for s in internal_covers)
                if minimum != cover:
                    continue
                edges = inside + [(a, cover + i) for i, s in enumerate(types) for a in range(cover) if s >> a & 1]
                nb = [{w for e in edges if v in e for w in e if v != w} for v in range(n)]
                if not all(nb) or any(sum(ns == {v} for ns in nb) > 1 for v in range(n)):
                    continue
                result[(internal, types)] = (n, len(edges), edges)
    return sorted(result.values())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cover", type=int, choices=(3, 4), default=3)
    parser.add_argument("--max-vertices", type=int)
    args = parser.parse_args()
    for i, (n, m, edges) in enumerate(kernels(args.cover, args.max_vertices)):
        print(i, n, m, args.cover, *(v for edge in edges for v in edge))
