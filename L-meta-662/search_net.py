"""Search nine-gate monotone circuits for the triangle with a private leaf at each vertex.

The output is the AND of two three-literal disjunctions and one disjunction of two
literals with a two-literal product. Each candidate has three AND gates and six
wide OR gates. Truth tables are 64-bit integers, one bit per assignment.
"""

from itertools import combinations


def main():
    vertices = range(6)
    edges = ((0, 1), (0, 2), (1, 2), (0, 5), (1, 4), (2, 3))
    inputs = [
        sum(1 << mask for mask in range(64) if mask & (1 << v))
        for v in vertices
    ]
    target = 0
    for u, v in edges:
        target |= inputs[u] & inputs[v]

    # Each conjunct must individually accept every edge.
    clauses = []
    for a, b, c in combinations(vertices, 3):
        table = inputs[a] | inputs[b] | inputs[c]
        if target & ~table == 0:
            clauses.append(((a, b, c), table))

    matches = []
    for a, b in combinations(vertices, 2):
        remaining = [v for v in vertices if v not in (a, b)]
        for c, d in combinations(remaining, 2):
            gate = inputs[a] | inputs[b] | (inputs[c] & inputs[d])
            if target & ~gate:
                continue
            for (first, p), (second, q) in combinations(clauses, 2):
                if gate & p & q == target:
                    matches.append(((a, b), (c, d), first, second))

    if not matches:
        raise SystemExit("No circuit in this family matched.")
    print(f"Found {len(matches)} circuits matching all 64 assignments.")
    for literals, product, first, second in matches:
        print(f"OR {literals} with AND {product}, then intersect with OR {first} and OR {second}")


if __name__ == "__main__":
    main()
