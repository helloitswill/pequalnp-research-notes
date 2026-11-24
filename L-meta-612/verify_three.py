"""Independent full-truth-table search on the kernels produced by cover_three.py."""
from functools import lru_cache
from itertools import combinations

from cover_kernels import kernels


def reaches(n, edges, budget):
    masks = [1 << a | 1 << b for a, b in edges]
    inputs = range(1 << n)
    positives = {x for x in inputs if any(x & mask == mask for mask in masks)}
    negatives = [x for x in inputs if x not in positives and
                 all(x & (1 << v) or (x | (1 << v)) in positives for v in range(n))]
    target = sum(1 << x for x in positives)
    initial = tuple(sorted(sum(1 << x for x in inputs if x & (1 << v)) for v in range(n)))
    required = (1 << (len(edges) * len(negatives))) - 1

    @lru_cache(None)
    def distinguished(w):
        reject = sum(1 << j for j, x in enumerate(negatives) if not w >> x & 1)
        return sum(reject << (i * len(negatives)) for i, x in enumerate(masks) if w >> x & 1)

    @lru_cache(None)
    def visit(wires, remaining):
        if target in wires:
            return True
        if remaining <= 0 or len(wires) - 1 > remaining:
            return False
        for a, b in combinations(wires, 2):
            others = tuple(w for w in wires if w != a and w != b)
            base = 0
            for w in others:
                base |= distinguished(w)
            for out in (a | b, a & b):
                if out in wires:
                    continue
                sep = base | distinguished(out)
                for keep in [(), (a,), (b,), (a, b)]:
                    if len(others) + len(keep) + 1 > remaining:
                        continue
                    possible = sep
                    for w in keep:
                        possible |= distinguished(w)
                    if possible == required and visit(tuple(sorted(others + keep + (out,))), remaining - 1):
                        return True
        return False

    result = visit(initial, budget)
    visit.cache_clear()
    distinguished.cache_clear()
    return result


if __name__ == "__main__":
    graphs = kernels()
    for i, (n, m, edges) in enumerate(graphs):
        if reaches(n, edges, m + 1):
            raise SystemExit(f"Counterexample on kernel {i}: {edges}")
    print(f"Full truth tables exclude the below-bound budget on all {len(graphs)} kernels.")
