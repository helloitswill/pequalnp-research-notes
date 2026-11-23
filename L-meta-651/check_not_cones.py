"""Necessary-input test for local NOT-containing replacements in L-meta-587.

Each gate produces wire 10+j. Only inputs crossing the original cone's cut
may be used by its replacement. A support test and a read-once polarity test
exclude local replacements without enumerating gate lists.
"""
from itertools import combinations, islice


# PEqualNP.Outside.L_meta_587 at 3ec921591ffc6536fad46069ec0c219464fb6ffc.
GATES = [
    ('or', 7, 3), ('or', 1, 5), ('or', 1, 9), ('or', 3, 6),
    ('or', 1, 10), ('or', 5, 9), ('or', 13, 5), ('and', 11, 0),
    ('or', 9, 0), ('or', 18, 3), ('and', 12, 6), ('and', 2, 14),
    ('and', 15, 7), ('and', 8, 16), ('or', 22, 20), ('and', 4, 19),
    ('or', 23, 17), ('or', 21, 26), ('or', 25, 27), ('or', 24, 28),
]
EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
         (5,7),(7,9),(9,6),(6,8),(8,5)]
N = 10
ROWS = 1 << N
FULL = (1 << ROWS) - 1


def evaluate(inputs, override=None):
    values = list(inputs)
    for j, (op, a, b) in enumerate(GATES, N):
        if override is not None and override[0] == j:
            value = override[1]
        else:
            value = values[a] & values[b] if op == 'and' else values[a] | values[b]
        values.append(value)
    return values


def truth_tables():
    inputs = [sum(1 << row for row in range(ROWS) if row & (1 << i))
              for i in range(N)]
    target = sum(1 << row for row in range(ROWS)
                 if any(row & (1 << a) and row & (1 << b) for a,b in EDGES))
    tables = evaluate(inputs)
    assert tables[-1] == target
    return inputs, target, tables


def cones_by_size():
    # A cone grows backwards from its root. Absorb a gate only if its one
    # use is inside the cone. Thus no internal gate is shared or used outside.
    uses = [0] * (N + len(GATES))
    for _, a, b in GATES:
        uses[a] += 1
        uses[b] += 1
    current = {frozenset([wire]) for wire in range(N, len(uses))}
    while current:
        yield current
        following = set()
        for cone in current:
            for wire in cut(cone):
                if wire >= N and uses[wire] == 1:
                    following.add(cone | {wire})
        current = following


def cut(cone):
    return {operand for wire in cone for operand in GATES[wire-N][1:]
            if operand not in cone}


def permits_function(tables, subset, care, want):
    # Refine the cared-for rows into cells with identical selected signals.
    # A Boolean function is possible exactly when every cell has one label.
    cells = [care]
    for wire in subset:
        value = tables[wire]
        cells = [part for cell in cells for part in (cell & value, cell & ~value)
                 if part]
    return not any((cell & want) and (cell & ~want) for cell in cells)


def forced_positive(tables, subset, care, want):
    # For every cut wire find two cared-for input rows inducing the same
    # values on all other selected wires, but demanding an increase on it.
    labels = {}
    for row in range(ROWS):
        if (care >> row) & 1:
            code = sum(((tables[wire] >> row) & 1) << bit
                       for bit, wire in enumerate(subset))
            label = (want >> row) & 1
            if code in labels:
                assert labels[code][0] == label
            labels[code] = (label, row)
    witnesses = {}
    for bit, wire in enumerate(subset):
        mask = 1 << bit
        for code, (label, row) in labels.items():
            if code & mask or label:
                continue
            upper = labels.get(code | mask)
            if upper is not None and upper[0]:
                witnesses[wire] = (row, upper[1])
                break
    return witnesses


def main():
    inputs, target, tables = truth_tables()
    cofactors = {}
    for root in range(N, N + len(GATES)):
        lo = evaluate(inputs, (root, 0))[-1]
        hi = evaluate(inputs, (root, FULL))[-1]
        care = lo ^ hi
        assert ((target ^ lo) & ~care) == 0
        cofactors[root] = care, (target ^ lo) & care
    print('Verified the 20-gate circuit on all 1024 assignments.')
    print('size | cones | subsets tested | support passes | polarity exclusions | unresolved cones')
    for k, cones in enumerate(islice(cones_by_size(), 8), 1):
        if k < 2:
            continue
        tested = passing = excluded = 0
        unresolved = 0
        polarity_example = None
        for cone in sorted(tuple(sorted(cone)) for cone in cones):
            frontier = sorted(cut(cone))
            # Any candidate with g <= k-1 gates, at least one live unary NOT
            # and the rest of fan-in <= 2 has at most g distinct input wires.
            largest = min(k-1, len(frontier))
            care, want = cofactors[cone[-1]]
            all_excluded = True
            for subset in combinations(frontier, largest):
                tested += 1
                if not permits_function(tables, subset, care, want):
                    continue
                passing += 1
                if len(subset) == k-1:
                    witnesses = forced_positive(tables, subset, care, want)
                    if len(witnesses) == k-1:
                        # Equality in the fan-in count forces a read-once
                        # tree with exactly one NOT, so at least one input
                        # would have negative polarity. Every witness forbids it.
                        excluded += 1
                        polarity_example = cone, witnesses
                        continue
                all_excluded = False
            if not all_excluded:
                unresolved += 1
        print(f'{k:4} | {len(cones):5} | {tested:14} | {passing:14} | '
              f'{excluded:19} | {unresolved:16}')
        assert unresolved == 0, "A candidate remained after the two tests."
        if k < 8:
            assert passing == 0
        else:
            assert passing == excluded == 1
            cone, witnesses = polarity_example
            assert cone == (11, 14, 16, 17, 21, 23, 26, 27)
            assert set(witnesses) == {0, 1, 2, 5, 8, 10, 13}
            care, want = cofactors[cone[-1]]
            for wire, (lo, hi) in witnesses.items():
                assert ((care >> lo) & (care >> hi) & 1) == 1
                assert (want >> lo) & 1 == 0 and (want >> hi) & 1 == 1
                for w in witnesses:
                    low_value = (tables[w] >> lo) & 1
                    high_value = (tables[w] >> hi) & 1
                    if w == wire:
                        assert (low_value, high_value) == (0, 1)
                    else:
                        assert low_value == high_value
            print('Size-eight positive influence witnesses:', witnesses)


if __name__ == '__main__':
    main()
