"""Check separated circuits and their four-gate row extensions against the merged edge list."""

from functools import reduce
from operator import or_


# Consecutive triples of line indices in the edgeList of L_meta_6659.lean.
MERGED_ROWS = ((0, 1, 3), (0, 2, 6), (1, 5, 6), (0, 4, 5),
               (3, 4, 6), (2, 3, 5), (1, 2, 4))


def add_rows(gates, out, points):
    def emit(op, a, b):
        wire = 14 + len(gates)
        assert 0 <= a < wire and 0 <= b < wire and a != b
        gates.append((op, a, b))
        return wire

    for p in points:
        a, b, c = (7 + l for l in range(7) if (p + l) % 7 in (0, 1, 3))
        lines = emit('or', emit('or', a, b), c)
        star = emit('and', p, lines)
        out = star if out is None else emit('or', out, star)
    return out


def evaluate(inputs, gates, out):
    wires = list(inputs)
    point_wires = set(range(7))
    line_wires = set(range(7, 14))
    for op, a, b in gates:
        if op == 'and':
            assert a in point_wires and b in line_wires
            wires.append(wires[a] & wires[b])
        else:
            if a in line_wires and b in line_wires:
                line_wires.add(len(wires))
            wires.append(wires[a] | wires[b])
    return wires[out]


def main():
    # Bit x of each integer stores the wire value on the 14-bit input x.
    count = 1 << 14
    all_on = (1 << count) - 1
    inputs = []
    for i in range(14):
        run = 1 << i
        pattern = ((1 << run) - 1) << run
        inputs.append(pattern * (all_on // ((1 << (2 * run)) - 1)))
    row_values = [inputs[p] & reduce(or_, (inputs[7+l] for l in neighbors))
                  for p, neighbors in enumerate(MERGED_ROWS)]
    full = reduce(or_, row_values)
    for mask in range(1, 1 << 7):
        chosen = [p for p in range(7) if mask >> p & 1]
        rest = [p for p in range(7) if not mask >> p & 1]
        gates = []
        out = add_rows(gates, None, chosen)
        assert len(gates) == 4 * len(chosen) - 1
        assert evaluate(inputs, gates, out) == reduce(or_, (row_values[p] for p in chosen))
        size = len(gates)
        out = add_rows(gates, out, rest)
        assert len(gates) - size == 4 * len(rest)
        assert len(gates) == 27 and evaluate(inputs, gates, out) == full
    print('127 nonempty row subsets; all 16,384 inputs verified for each.')
    print('Separated size 4k-1; restoring each omitted row costs four gates.')


if __name__ == '__main__':
    main()
