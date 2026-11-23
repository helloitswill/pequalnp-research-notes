"""Verify every hypothesis and the failed inequality for the L-meta-662 net graph.

Requires Python 3. No packages or network access. The six primary wires are
a,b,c,d,e,f in order. Each gate j appends wire 6+j, just as Circuit.wires does.
"""
from itertools import product

NAMES = "abcdef"
N = len(NAMES)
EDGES = {(0, 1), (0, 2), (1, 2), (0, 5), (1, 4), (2, 3)}
GATES = [
    ("OR",  (0, 1)),    # 6  = a OR b
    ("AND", (2, 3)),    # 7  = c AND d
    ("OR",  (4, 0)),    # 8  = e OR a
    ("OR",  (5, 1)),    # 9  = f OR b
    ("OR",  (6, 7)),    # 10 = a OR b OR (c AND d)
    ("OR",  (2, 8)),    # 11 = c OR e OR a
    ("OR",  (9, 2)),    # 12 = f OR b OR c
    ("AND", (10, 11)),  # 13 = first AND second clause
    ("AND", (12, 13)),  # 14 = all three clauses
]
OUTPUT = 14


def require(condition, message):
    if not condition:
        raise ValueError(message)


def adjacent(u, v):
    return (min(u, v), max(u, v)) in EDGES


def run_circuit(bits):
    wires = list(bits)
    for op, inputs in GATES:
        require(op in ("AND", "OR") and len(inputs) <= 2, "Gate outside Monotone2")
        require(all(0 <= i < len(wires) for i in inputs), "Invalid wire reference")
        values = [wires[i] for i in inputs]
        wires.append(all(values) if op == "AND" else any(values))
    return wires


def main():
    require(all(0 <= u < v < N for u, v in EDGES), "Invalid simple graph edge")
    for a, b, c, e in product(range(N), repeat=4):
        walk = adjacent(a, b) and adjacent(b, c) and adjacent(c, e) and adjacent(e, a)
        require(not walk or a == c or b == e, "The graph has a 4-cycle")

    covers = []
    for bits in product((False, True), repeat=N):
        if all(bits[u] or bits[v] for u, v in EDGES):
            covers.append(sum(bits))
        expected = any(bits[u] and bits[v] for u, v in EDGES)
        require(run_circuit(bits)[OUTPUT] == expected, f"Wrong circuit output on {bits}")

    tau = min(covers)
    require(tau == 3, "Unexpected vertex cover number")
    singletons = [run_circuit([i == v for i in range(N)]) for v in range(N)]
    and_gates, wide_or, narrow_or = set(), set(), set()
    for j, (op, _) in enumerate(GATES):
        if op == "AND":
            and_gates.add(j)
        else:
            support = [NAMES[v] for v, wires in enumerate(singletons) if wires[N+j]]
            print(f"OR gate {j}: singleton support {''.join(support)}")
            (wide_or if len(support) >= 2 else narrow_or).add(j)
    require(and_gates == {1, 7, 8} and wide_or == {0, 2, 3, 4, 5, 6} and not narrow_or,
            "Unexpected gate index sets")

    weighted = len(and_gates) + len(wide_or) + 2 * len(narrow_or)
    lhs, rhs = len(EDGES) + 2 * tau, weighted + 2
    require((lhs, rhs) == (12, 11) and lhs > rhs, "Expected a violated lower bound")
    print(f"All 64 inputs correct; graph is 4-cycle-free; edges={len(EDGES)}, cover={tau}.")
    print(f"Weighted gate count={weighted}. Posted inequality requires {lhs} <= {rhs}: false.")


if __name__ == "__main__":
    main()
