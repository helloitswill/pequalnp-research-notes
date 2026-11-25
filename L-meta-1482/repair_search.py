"""Remove one gate and resynthesize any other gate in the fixed 65-gate circuit."""

import json
from itertools import combinations

from full_plane import all_inputs, boundary, build, marked_pairs, remove


def wires_after(gates, inputs, deleted, replacement):
    wires = list(inputs)
    for j, (op, a, b) in enumerate(gates):
        if j == deleted:
            wires.append(wires[replacement])
        else:
            wires.append(wires[a] & wires[b] if op == 'and' else wires[a] | wires[b])
    return wires


def forced_output(gates, old, start, value, deleted, replacement):
    wires = old[:26+start] + [value]
    for j in range(start+1, len(gates)):
        op, a, b = gates[j]
        if j == deleted:
            wires.append(wires[replacement])
        else:
            wires.append(wires[a] & wires[b] if op == 'and' else wires[a] | wires[b])
    return wires[-1]


def possible_gates(wires, end, skip, on, off):
    # An AND needs both operands on at every mandatory positive test. An OR
    # needs both operands off at every mandatory negative test.
    can_and = [i for i in range(end) if i != skip and wires[i] & on == on]
    for a, b in combinations(can_and, 2):
        if not (wires[a] & wires[b] & off):
            yield 'and', a, b
    can_or = [i for i in range(end) if i != skip and not (wires[i] & off)]
    for a, b in combinations(can_or, 2):
        if (wires[a] | wires[b]) & on == on:
            yield 'or', a, b


def search(gates, deletion_indices=None):
    inputs, truth, negatives = boundary()
    ones = (1 << (52 + negatives)) - 1
    duplicates = [(a, b) for _, a, b in gates]
    admissible = equivalent = marked = 0
    if deletion_indices is None:
        deletion_indices = range(len(gates))
    for deleted in deletion_indices:
        for replacement in range(26+deleted):
            dead_wire = 26+deleted
            bad = [j for j, args in enumerate(duplicates) if dead_wire in args and replacement in args]
            if len(bad) > 1:
                continue
            old = wires_after(gates, inputs, deleted, replacement)
            for h in (bad if bad else range(len(gates))):
                if h == deleted:
                    continue
                low = forced_output(gates, old, h, 0, deleted, replacement)
                if low & ~truth:
                    continue
                high = forced_output(gates, old, h, ones, deleted, replacement)
                if truth & ~high:
                    continue
                admissible += 1
                for g in possible_gates(old, 26+h, dead_wire, truth & ~low, high & ~truth):
                    revised = gates.copy()
                    revised[h] = g
                    if deleted == len(gates)-1:
                        if replacement < 26:
                            continue
                        candidate = revised[:replacement-25]
                    else:
                        candidate = remove(revised, deleted, replacement)
                    if candidate is None:
                        continue
                    equivalent += 1
                    if (pairs := marked_pairs(candidate)):
                        assert all_inputs(candidate) == 1 << 26
                        marked += 1
                        print(json.dumps(dict(deleted=deleted, replacement=replacement, edited=h,
                            gate=g, double_pairs=pairs, gates=candidate)), flush=True)
                        return admissible, equivalent, marked
    return admissible, equivalent, marked


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--diamond', action='store_true', help='Also replace a gate in the two-line subcircuit.')
    args = parser.parse_args()
    initial = build()
    if not args.diamond:
        print('feasible edit locations, equivalent repairs, qualifying repairs', search(initial))
    else:
        feasible = equivalent = cases = 0
        found = False
        local = [0, 1, 13, 14, 28, 31, 65, 66, 67]
        for h in (40, 41, 42):
            for a, b in combinations([i for i in local if i < h + 26], 2):
                for op in ('and', 'or'):
                    replacement = (op, a, b)
                    if replacement == initial[h]:
                        continue
                    case = initial.copy()
                    case[h] = replacement
                    nf, ne, nm = search(case, [i for i in (40, 41, 42) if i != h])
                    cases += 1
                    feasible += nf
                    equivalent += ne
                    if nm:
                        found = True
                        print('first edit', h, replacement)
                        raise SystemExit(0)
        print('first edits, feasible later locations, equivalent repairs, qualifying repairs',
              cases, feasible, equivalent, int(found))
