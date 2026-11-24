"""Construct the predicted upper-bound circuit and evaluate it on every input."""
import sys
from itertools import combinations


def check(n, edges, t):
    vertices = range(n)
    edges = [tuple(sorted(e)) for e in edges]
    cover = next(s for s in combinations(vertices, t) if all(a in s or b in s for a, b in edges))
    assert not any(all(a in s or b in s for a, b in edges) for s in combinations(vertices, t - 1))
    groups = {v: [] for v in cover}
    for a, b in edges:
        if a in groups:
            groups[a].append(b)
        else:
            groups[b].append(a)
    gates = []

    def put(kind, a, b):
        gates.append((kind, a, b))
        return n + len(gates) - 1

    def disjoin(wires):
        first, *rest = wires
        for w in rest:
            first = put("or", first, w)
        return first

    output = disjoin([put("and", v, disjoin(groups[v])) for v in cover])
    assert len(gates) == len(edges) + t - 1
    patterns = range(1 << n)
    wires = [sum(1 << x for x in patterns if x & (1 << v)) for v in vertices]
    for kind, a, b in gates:
        wires.append(wires[a] & wires[b] if kind == "and" else wires[a] | wires[b])
    expected = 0
    for a, b in edges:
        expected |= wires[a] & wires[b]
    assert wires[output] == expected


if __name__ == "__main__":
    count = 0
    for row in sys.stdin:
        _, n, m, t, *ends = map(int, row.split())
        assert len(ends) == 2 * m
        check(n, list(zip(ends[::2], ends[1::2])), t)
        count += 1
    assert count > 0
    print(f"Verified a circuit of the predicted size on every input for each of {count} graphs.")
