"""Verify the full 65-gate circuit and search its one-gate reductions."""

from functools import reduce
from operator import or_

from patch_search import marking


def points_on(line):
    return [(line + d) % 13 for d in (0, 1, 3, 9)]


def build():
    gates = []

    def gate(op, a, b):
        assert 0 <= a < 26 + len(gates) and 0 <= b < 26 + len(gates) and a != b
        gates.append((op, a, b))
        return 25 + len(gates)

    point_or = []
    for line in range(13):
        a, b, c, d = points_on(line)
        point_or.append(gate('or', gate('or', a, b), gate('or', c, d)))
    first = gate('and', 13, point_or[0])
    combined = gate('and', gate('or', first, point_or[1]), gate('or', first, 14))
    terms = [combined] + [gate('and', 13 + line, point_or[line]) for line in range(2, 13)]
    output = reduce(lambda a, b: gate('or', a, b), terms)
    assert output == 25 + len(gates)
    return gates


def evaluate(gates, bits, bypass=None):
    wires = list(bits)
    for j, (op, a, b) in enumerate(gates):
        if bypass is not None and j == bypass[0]:
            wires.append(wires[bypass[1]])
        else:
            wires.append(wires[a] & wires[b] if op == 'and' else wires[a] | wires[b])
    return wires[-1]


def incidence_masks():
    return [sum(1 << line for line in range(13) if p in points_on(line)) for p in range(13)]


def all_inputs(gates):
    # A bit in a machine-independent Python integer represents a line mask.
    line_bits = [sum(1 << mask for mask in range(1 << 13) if mask >> i & 1) for i in range(13)]
    ones = (1 << (1 << 13)) - 1
    neighbors = incidence_masks()
    expected = [0] * (1 << 13)
    point_tables = [reduce(or_, (line_bits[j] for j in range(13) if row >> j & 1)) for row in neighbors]
    for mask in range(1 << 13):
        if mask:
            first = mask & -mask
            expected[mask] = expected[mask ^ first] | point_tables[first.bit_length() - 1]
        inputs = [ones if mask >> p & 1 else 0 for p in range(13)] + line_bits
        assert evaluate(gates, inputs) == expected[mask], mask
    return 1 << 26


def marked_pairs(gates):
    return [(p, line) for line in range(13) for p in points_on(line)
            if not marking(gates, 26, p, 13 + line) and not marking(gates, 26, 13 + line, p)]


def boundary():
    edges = [(1 << p) | (1 << (13 + line)) for line in range(13) for p in points_on(line)]
    neighbors = incidence_masks()
    negative = []
    for points in range(1 << 13):
        used = reduce(or_, (row for p, row in enumerate(neighbors) if points >> p & 1), 0)
        lines = ((1 << 13) - 1) ^ used
        if all(points >> p & 1 or row & lines for p, row in enumerate(neighbors)):
            negative.append(points | (lines << 13))
    tests = edges + negative
    bits = [sum(1 << i for i, mask in enumerate(tests) if (mask >> j) & 1) for j in range(26)]
    return bits, (1 << len(edges)) - 1, len(negative)


def remove(gates, j, replacement):
    """Remove gate j, route all its uses to replacement, and reindex the wires."""
    dead = j + 26
    def renumber(i):
        return replacement if i == dead else i - (i > dead)
    new = []
    for k, (op, a, b) in enumerate(gates):
        if k == j:
            continue
        a, b = sorted([renumber(a), renumber(b)])
        if a == b:
            return None
        new.append((op, a, b))
    return new


def one_gate_search(gates):
    bits, truth, negatives = boundary()
    assert evaluate(gates, bits) == truth
    checked = equivalent = 0
    found = []
    for j in range(len(gates)):
        for r in range(26 + j):
            checked += 1
            if evaluate(gates, bits, (j, r)) != truth:
                continue
            equivalent += 1
            if j == len(gates) - 1:
                # The new output may be an input or an earlier gate.
                if r < 26:
                    continue
                next_gates = gates[:r-25]
            else:
                next_gates = remove(gates, j, r)
            if next_gates is not None and (pairs := marked_pairs(next_gates)):
                assert all_inputs(next_gates) == 1 << 26
                found.append((j, r, pairs))
    return negatives, checked, equivalent, found


if __name__ == '__main__':
    circuit = build()
    print('gates', len(circuit), 'full inputs checked', all_inputs(circuit), 'double-marked pairs', marked_pairs(circuit))
    print('maximal negative tests, substitutions, equivalent substitutions, qualifying replacements', one_gate_search(circuit))
