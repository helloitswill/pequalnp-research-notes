"""Check finite members of the L-meta-662 family and all local truth patterns."""
from collections import deque
from itertools import combinations, product


def check_local_patterns():
    for x0, x1, x2, h0, h1, h2 in product((False, True), repeat=6):
        p = (x0 or x1) or (x2 and h2)
        q = (x0 or x2) or h1
        r = (x1 or x2) or h0
        edge = (x0 and x1) or (x1 and x2) or (x2 and x0)
        edge = edge or (x0 and h0) or (x1 and h1) or (x2 and h2)
        assert (p and q and r) == edge


def check_member(d, m):
    assert d >= 2 and m > 2**d
    shifts = [2**j - 1 for j in range(d)]
    n = 6 * m
    mid = 3 * m
    adj = [set() for _ in range(n)]

    def add_edge(v, w):
        assert v != w and w not in adj[v]
        adj[v].add(w)
        adj[w].add(v)

    for i in range(m):
        for k in range(3):
            v = 3*i + k
            add_edge(v, 3*i + (k + 1) % 3)
            for delta in shifts:
                add_edge(v, mid + 3*((i + delta) % m) + k)

    assert sum(map(len, adj)) == 2 * 3*m*(d + 1)
    assert all(len(adj[v]) == d + (2 if v < mid else 0) for v in range(n))
    assert all(max(adj[v]) < mid and v-mid in adj[v] for v in range(mid, n))
    assert all(len(adj[v] & adj[w]) <= 1 for v, w in combinations(range(n), 2))
    reached = {0}
    queue = deque([0])
    while queue:
        new = adj[queue.popleft()] - reached
        reached.update(new)
        queue.extend(new)
    assert len(reached) == n

    # Encode all singleton and pair assignments in parallel, one bit per row.
    wires = [1 << v for v in range(n)]
    singles = (1 << n) - 1
    expected = 0
    for j, (v, w) in enumerate(combinations(range(n), 2), start=n):
        flag = 1 << j
        wires[v] |= flag
        wires[w] |= flag
        if w in adj[v]:
            expected |= flag

    counts = {'and': 0, 'wide': 0, 'narrow': 0}

    def and_gate(a, b):
        counts['and'] += 1
        return a & b

    def or_gate(a, b):
        val = a | b
        counts['wide' if bin(val & singles).count('1') >= 2 else 'narrow'] += 1
        return val

    def or_chain(values):
        out = values[0]
        for val in values[1:]:
            out = or_gate(out, val)
        return out

    outputs = []
    for i in range(m):
        centers = [3*i + k for k in range(3)]
        hs = [or_chain([wires[mid + 3*((i+s) % m) + k] for s in shifts]) for k in range(3)]
        x, y, z = (wires[v] for v in centers)
        p = or_gate(or_gate(x, y), and_gate(z, hs[2]))
        q = or_gate(or_gate(x, z), hs[1])
        r = or_gate(or_gate(y, z), hs[0])
        outputs.append(and_gate(and_gate(p, q), r))
    assert or_chain(outputs) == expected
    assert counts == {'and': 3*m, 'wide': (3*d+3)*m, 'narrow': m-1}
    weight = counts['and'] + counts['wide'] + 2 * counts['narrow']
    assert 3*m*(d+1) + 2*(3*m) - 2 - weight == m
    return n + n*(n-1)//2


if __name__ == '__main__':
    check_local_patterns()
    instances = [(2, 5), (2, 8), (3, 9), (3, 13), (4, 17), (5, 33)]
    rows = sum(check_member(d, m) for d, m in instances)
    print(f'Verified all 64 local assignments and {rows} singleton/pair assignments '
          f'across {len(instances)} connected graphs.')
