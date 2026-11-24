"""Check positive-control gate traces on every Boolean input."""
import argparse
from pathlib import Path


def check(graph, budget, operations, smaller_optimal=False):
    n, edges = graph
    edge_masks = [(1 << a) | (1 << b) for a, b in edges]
    patterns = range(1 << n)
    positives = {x for x in patterns if any(x & mask == mask for mask in edge_masks)}
    negatives = [x for x in patterns if x not in positives and
                 all(x & (1 << v) or (x | (1 << v)) in positives for v in range(n))]
    boundary = edge_masks + negatives
    if smaller_optimal:
        boundary.extend(((1 << n) - 1) ^ (1 << v) for v in range(n))

    def signature(wire):
        return sum(((wire >> x) & 1) << i for i, x in enumerate(boundary))

    wires = {}
    for v in range(n):
        column = sum(1 << x for x in patterns if x & (1 << v))
        wires[signature(column)] = column
    for op in operations:
        out, equals, a, kind, b = op.split()
        assert equals == "=" and kind in ("AND", "OR")
        left, right = wires[int(a)], wires[int(b)]
        column = left & right if kind == "AND" else left | right
        assert int(out) == signature(column)
        wires[int(out)] = column
    assert len(operations) <= budget
    target = sum(1 << x for x in positives)
    assert wires[signature(target)] == target


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graphs", type=Path)
    parser.add_argument("transcript", type=Path)
    parser.add_argument("--smaller-optimal", action="store_true")
    args = parser.parse_args()
    graphs = {}
    for row in args.graphs.read_text().splitlines():
        i, n, m, cover, *vertices = map(int, row.split())
        assert len(vertices) == 2 * m and i not in graphs
        graphs[i] = (n, list(zip(vertices[::2], vertices[1::2])), m + cover - 1)
    groups = {}
    for row in args.transcript.read_text().splitlines():
        if row.startswith("kernel "):
            fields = row.split()
            i, budget = int(fields[1]), int(fields[7])
            n, edges, target_budget = graphs[i]
            assert fields[8] == "FOUND" and i not in groups and budget == target_budget
            assert int(fields[3]) == n and int(fields[5]) == len(edges)
            groups[i] = []
        else:
            groups[i].append(row)
    assert groups.keys() == graphs.keys()
    for i, (n, edges, budget) in graphs.items():
        check((n, edges), budget, groups[i], args.smaller_optimal)
    print(f"All {len(groups)} positive-control circuits agree on every Boolean input.")


if __name__ == "__main__":
    main()
