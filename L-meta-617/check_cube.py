"""Exact gate minimization for the three-cube's edge function, allowing shared wires.

Python 3, standard library. For each trial wire, bits encode its outputs on the
positive and negative boundary assignments. No input symmetry is assumed.
"""
from functools import lru_cache
from itertools import combinations

N = 8
EDGES = tuple((a, b) for a, b in combinations(range(N), 2) if (a ^ b) in (1, 2, 4))

def cube(x):
    return any((x >> a) & (x >> b) & 1 for a, b in EDGES)

def minimize(limit):
    rows = [x for x in range(1 << N) if cube(x) and all(
        not cube(x ^ (1 << i)) for i in range(N) if (x >> i) & 1)]
    cols = [x for x in range(1 << N) if not cube(x) and all(
        cube(x | (1 << i)) for i in range(N) if not (x >> i) & 1)]
    examples = rows + cols
    target = (1 << len(rows)) - 1
    all_pairs = (1 << (len(rows) * len(cols))) - 1
    inputs = tuple(sum(((x >> i) & 1) << k for k, x in enumerate(examples))
                   for i in range(N))

    @lru_cache(None)
    def separated(wire):
        """Bit (i,j) is set when the wire is 1 for positive i and 0 for negative j."""
        off = ~(wire >> len(rows)) & ((1 << len(cols)) - 1)
        return sum(off << (i * len(cols)) for i in range(len(rows)) if wire >> i & 1)

    visited = set()
    calls = 0
    viable = 0
    def find(wires, left):
        nonlocal calls, viable
        calls += 1
        if target in wires:
            return []
        if left == 0 or len(wires) - 1 > left:
            return None
        key = (tuple(sorted(wires)), left)
        if key in visited:
            return None
        visited.add(key)
        for i, j in combinations(range(len(wires)), 2):
            a, b = wires[i], wires[j]
            others = tuple(w for k, w in enumerate(wires) if k not in (i, j))
            base = 0
            for w in others:
                base |= separated(w)
            for op, value in (('AND', a & b), ('OR', a | b)):
                # On this set of labeled examples this gate can be replaced by a
                # wire if equal. A constant can likewise be propagated. Since the
                # entire candidate is monotone, correctness on the boundary suffices.
                if value in wires or value in (0, (1 << len(examples)) - 1):
                    continue
                for kept in ((), (a,), (b,), (a, b)):
                    if len(others) + len(kept) + 1 > left:
                        continue
                    covered = base | separated(value)
                    for w in kept:
                        covered |= separated(w)
                    if covered != all_pairs:
                        continue
                    viable += 1
                    suffix = find(others + kept + (value,), left - 1)
                    if suffix is not None:
                        return [(op, a, b, value)] + suffix
        return None

    gates = find(inputs, limit)
    print(f"budget={limit} positives={len(rows)} negatives={len(cols)} "
          f"expanded={len(visited)} admissible_moves={viable} calls={calls} "
          f"result={'NONE' if gates is None else 'FOUND'}")
    if gates is not None:
        idx = {value: i for i, value in enumerate(inputs)}
        circuit = []
        for op, a, b, result in gates:
            circuit.append((op, idx[a], idx[b]))
            idx[result] = N + len(circuit) - 1
        output = idx[target]
        for x in range(1 << N):
            values = [(x >> i) & 1 for i in range(N)]
            for op, a, b in circuit:
                values.append(values[a] & values[b] if op == 'AND' else values[a] | values[b])
            assert values[output] == cube(x)
        print(f"Checked on 256 inputs: {circuit}, output={output}.")
    return gates is not None

if __name__ == '__main__':
    import sys
    for budget in (map(int, sys.argv[1:]) if sys.argv[1:] else (10, 11, 12)):
        minimize(budget)
