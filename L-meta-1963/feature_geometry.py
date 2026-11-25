"""Finite geometry for the 13-feature and 25-mixed-gate bounds."""

from itertools import combinations
from math import comb


VERTICES = frozenset(range(13))
LINES = tuple(frozenset((start + d) % 13 for d in (0, 1, 3, 9)) for start in range(13))
PENCILS = tuple(frozenset(i for i, line in enumerate(LINES) if v in line) for v in range(13))
QUADS = tuple(frozenset(q) for q in combinations(range(13), 4)
              if all(len(set(q) & line) <= 2 for line in LINES))
EXTERIORS = tuple(frozenset(i for i, line in enumerate(LINES) if line.isdisjoint(q))
                  for q in QUADS)


def check_shore(tests, collinear_sets, incidence_count):
    assert len(tests) == len(set(tests)) == 234
    assert all(sum(v in test for test in tests) == incidence_count for v in VERTICES)
    for size in (1, 2, 3):
        for elements in combinations(VERTICES, size):
            vertices = set(elements)
            if size == 3 and any(vertices <= line for line in collinear_sets):
                continue
            extensions = [test for test in tests if vertices <= test]
            # Their intersection is exactly the points forced by containment.
            assert extensions and frozenset.intersection(*extensions) == vertices


def partitions(vertices):
    if not vertices:
        yield ()
        return
    first = min(vertices)
    for a, b in combinations(sorted(vertices - {first}), 2):
        group = frozenset((first, a, b))
        for remainder in partitions(vertices - group):
            yield (group,) + remainder


def check_extremal_point_codes():
    others = VERTICES - {0}
    quads = [q for q in QUADS if 0 not in q]
    hit = {frozenset(s): sum(1 << i for i, q in enumerate(quads) if not q.isdisjoint(s))
           for s in combinations(others, 3)}
    pencil = frozenset(line - {0} for line in LINES if 0 in line)
    count = 0
    no_transversal = []
    for parts in partitions(others):
        count += 1
        a, b, c, d = (hit[s] for s in parts)
        if not (a & b & c & d):
            no_transversal.append(frozenset(parts))
    assert count == 15400 and no_transversal == [pencil]
    print("15,400 partitions at point 0; only the original pencil excludes every transversal quadrangle.")


def check_exterior_subsets():
    pairs = 0
    noncollinear_triples = 0
    collinear_triples = 0
    examples = 0
    for line in LINES:
        exterior = [q for q in QUADS if q.isdisjoint(line)]
        assert len(exterior) == 54
        for a, b in combinations(sorted(VERTICES - line), 2):
            assert sum(a in q and b in q for q in exterior) == 9
            pairs += 1
        exceptions = {other - line for other in LINES if other != line}
        assert len(exceptions) == 12
        for triple in combinations(sorted(VERTICES - line), 3):
            selected = frozenset(triple)
            count = sum(selected <= q for q in exterior)
            if selected in exceptions:
                assert count == 0
                collinear_triples += 1
            else:
                assert count == 3
                noncollinear_triples += 1

        # On an auxiliary line, the three points outside this line are collinear.
        # Either operand can accept an exterior test, but their conjunction cannot.
        for other in LINES:
            if other == line:
                continue
            a, b, c = sorted(other - line)
            def operands(points):
                line_hit = not points.isdisjoint(line)
                return (line_hit or (a in points and b in points),
                        line_hit or c in points)

            assert any(operands(q)[0] for q in exterior)
            assert any(operands(q)[1] for q in exterior)
            assert all(not all(operands(q)) for q in exterior)
            assert all(all(operands({p})) == (p in line) for p in VERTICES)
            assert all(not operands({p})[0] for p in VERTICES - line)
            examples += 1
    assert (pairs, noncollinear_triples, collinear_triples, examples) == (468, 936, 156, 156)
    print("Each of the 468 line/exterior-pair choices has nine quadrangles avoiding the line; "
          "all 156 nested-AND examples satisfy the stated line tests.")
    print("Of 1,092 line/exterior-triple choices, 936 occur in three exterior quadrangles "
          "each. The other 156 are the collinear triples.")


def check_mixed_upper():
    # Gate indices 0..25 are primary wires. Every generated OR for a line's
    # point sum is point-only. The incident flag at a chosen line witnesses
    # dependence on each shore for its AND and every output OR containing it.
    gates = []

    def add(op, a, b):
        index = 26 + len(gates)
        assert a < index and b < index and a != b
        gates.append((op, a, b))
        return index

    terms = []
    for index, line in enumerate(LINES):
        first, *remaining = sorted(line)
        for v in remaining:
            first = add("or", first, v)
        terms.append(add("and", first, 13 + index))
    output = terms[0]
    for term in terms[1:]:
        output = add("or", output, term)
    assert len(gates) == 64
    rows = [(set((p,)), set((i,)), True) for i, line in enumerate(LINES) for p in line]
    rows.extend((q, exterior, False) for q, exterior in zip(QUADS, EXTERIORS))
    for points, lines, expected in rows:
        wires = [p in points for p in range(13)] + [i in lines for i in range(13)]
        for op, a, b in gates:
            wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
        assert wires[output] == expected
    print("64-gate construction passes all 286 rows: 39 point-only ORs and 25 mixed gates.")


if __name__ == "__main__":
    assert all(len(exterior) == 3 and set.union(*(set(LINES[i]) for i in exterior)) == VERTICES - q
               for q, exterior in zip(QUADS, EXTERIORS))
    assert all(len(LINES[line] - set.union(*(set(LINES[i]) for i in exterior - {line}))) == 2
               for exterior in EXTERIORS for line in exterior)
    check_shore(QUADS, LINES, 72)
    check_shore(EXTERIORS, PENCILS, 54)
    assert comb(7, 3) == 35 and comb(8, 4) == 70
    print("All off-vertex extensions verified on both shores; singleton frequencies are 72 and 54.")
    check_extremal_point_codes()
    check_exterior_subsets()
    check_mixed_upper()
