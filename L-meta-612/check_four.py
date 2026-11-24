"""Exact four-input test of the counting argument for L-meta-612. Python 3."""
from itertools import combinations


N = 4
PAIRS = list(combinations(range(N), 2))
ALL = list(range(1 << N))
INPUTS = [sum(1 << x for x in ALL if x & (1 << v)) for v in range(N)]
LIMIT = 5


def graph_targets():
    by_function = {}
    for graph in range(1, 1 << len(PAIRS)):
        edges = [p for j, p in enumerate(PAIRS) if graph >> j & 1]
        neighbors = [{v for e in edges if u in e for v in e if u != v} for u in range(N)]
        if any(len(neighbors[u] & neighbors[v]) > 1 for u, v in PAIRS):
            continue
        truth = sum(1 << x for x in ALL if any(x >> u & x >> v & 1 for u, v in edges))
        cover = min(s.bit_count() for s in ALL if all((s >> u | s >> v) & 1 for u, v in edges))
        by_function[truth] = (graph, len(edges) + cover - 1)
    return by_function


def classify(gates, graph):
    support = [1 << i for i in range(N)]
    for meet, a, b in gates:
        support.append(0 if meet else support[a] | support[b])
    live = {N + len(gates) - 1}
    covered = products = safe = merges = other = 0
    for i in reversed(range(len(gates))):
        if N + i not in live:
            continue
        meet, a, b = gates[i]
        live.update([a, b])
        left, right = support[a], support[b]
        if not (left and right):
            other += 1
        elif not meet:
            merges += 1
        else:
            products += 1
            rectangle = sum(1 << j for j, (u, v) in enumerate(PAIRS)
                            if (left >> u & right >> v | left >> v & right >> u) & 1)
            if left & right == 0 and rectangle & ~graph == 0:
                safe += 1
                covered |= rectangle
    assert products <= other + 1
    assert covered.bit_count() <= merges + safe
    return covered


def search():
    targets = graph_targets()
    minima = {}
    counts = {}
    examples = {}
    wires = INPUTS.copy()
    gates = []

    def extend():
        for a, b in combinations(range(len(wires)), 2):
            left, right = wires[a], wires[b]
            for meet, f in ((True, left & right), (False, left | right)):
                if f in wires:
                    continue
                gates.append((meet, a, b))
                s = len(gates)
                if f in targets:
                    graph, _ = targets[f]
                    if s <= minima.get(graph, LIMIT + 1):
                        covered = classify(gates, graph)
                        if s < minima.get(graph, LIMIT + 1):
                            minima[graph] = s
                            counts[graph] = [0, 0]
                            examples.pop(graph, None)
                        counts[graph][int(covered != graph)] += 1
                        if covered != graph:
                            examples[graph] = gates.copy()
                if s < LIMIT:
                    wires.append(f)
                    extend()
                    wires.pop()
                gates.pop()

    extend()
    assert len(minima) == len(targets)
    assert all(minima[g] == bound for g, bound in targets.values())
    print(f"All {len(minima)} labelled nonempty four-vertex C4-free graphs attained |E| + tau - 1.")
    print(f"Optimal ordered circuits with every edge covered by a safe product: {sum(c[0] for c in counts.values())}")
    print(f"Optimal ordered circuits with a missing edge: {sum(c[1] for c in counts.values())}")
    if examples:
        g = min(examples)
        print("Example with a missing edge:", [p for i, p in enumerate(PAIRS) if g >> i & 1], examples[g])

    # The path ab,bc,cd also has this five-gate circuit. Its first product admits ad.
    path = sum(1 << PAIRS.index(e) for e in [(0, 1), (1, 2), (2, 3)])
    filtered = [(False, 0, 2), (False, 1, 3), (True, 4, 5), (False, 1, 2), (True, 6, 7)]
    values = INPUTS.copy()
    for meet, a, b in filtered:
        values.append(values[a] & values[b] if meet else values[a] | values[b])
    assert targets[values[-1]][0] == path and classify(filtered, path) == 0
    print("The five-gate path circuit computes the target with zero safe-product edges.")


if __name__ == "__main__":
    search()
