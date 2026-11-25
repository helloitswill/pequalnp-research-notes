"""Minimum extra binary gates for two line masks after eleven pure-OR cones are free."""
from itertools import combinations


def successors(wires):
    unions = {a | b for a, b in combinations(wires, 2)}
    intersections = {a & b for a, b in combinations(wires, 2)}
    return unions | intersections


def close_targets(wires, targets):
    # Charge the first occurrence of each of the two targets separately. Once a
    # target is producible, revealing it at once allows every possible later use.
    wires = set(wires)
    while True:
        outputs = successors(wires)
        new_targets = (outputs & targets) - wires
        if not new_targets:
            return targets <= wires, outputs - wires
        wires.update(new_targets)


def check_geometry():
    lines = [{(w + d) % 13 for d in (0, 1, 3, 9)} for w in range(13)]
    for a, b in combinations(lines, 2):
        common = a & b
        assert len(common) == 1
        expected = {frozenset(common)}
        expected.update(frozenset((u, v)) for u in a - b for v in b - a)
        actual = {frozenset(line & (a | b)) for line in lines if line != a and line != b}
        assert actual == expected


def main():
    check_geometry()
    common = 1
    a = (2, 4, 8)
    b = (16, 32, 64)
    targets = {common | sum(a), common | sum(b)}
    # Primary wires, constants of both signs, and every allowed cross-pair.
    free = {0, 127, common, *a, *b, *(u | v for u in a for v in b)}
    assert free.isdisjoint(targets)
    states = {frozenset()}
    counts = []
    for depth in range(4):
        counts.append(len(states))
        next_states = set()
        for intermediates in states:
            solved, new = close_targets(free | intermediates, targets)
            if solved:
                raise ValueError(f"Targets reached using {depth} nontarget gates: {intermediates}")
            if depth < 3:
                next_states.update(intermediates | {v} for v in new)
        states = next_states
    assert counts == [1, 48, 1386, 30391]
    print("Distinct states with 0, 1, 2, and 3 nontarget intermediates:", *counts)

    # Four explicit nontarget gates. Each target then takes one final OR.
    upper = (a[0] | a[1], a[0] | a[1] | a[2], b[0] | b[1], b[0] | b[1] | b[2])
    wires = set(free)
    for v in upper:
        assert v in successors(wires)
        wires.add(v)
    assert targets <= successors(wires)
    print("All 78 choices of two lines verified. Exact extra gate count: 6.")


if __name__ == "__main__":
    main()
