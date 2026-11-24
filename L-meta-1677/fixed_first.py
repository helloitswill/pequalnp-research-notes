"""Encode bounded AND/OR/NOT synthesis for the assigned Petersen graph as DIMACS."""
import argparse
from itertools import combinations
from pathlib import Path


EDGES = ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
         (3, 8), (5, 7), (6, 8), (8, 5))
WITNESS = (("or", 0, 6), ("or", 2, 9), ("and", 1, 10), ("or", 4, 5),
           ("and", 0, 12), ("or", 2, 4), ("or", 8, 14), ("and", 3, 15),
           ("or", 2, 5), ("and", 7, 17), ("or", 5, 6), ("and", 8, 19),
           ("or", 11, 13), ("or", 16, 21), ("or", 18, 22), ("or", 20, 23))


def target(x):
    return any(x & (1 << a) and x & (1 << b) for a, b in EDGES)


def check_witness():
    assert len(WITNESS) == 16 and WITNESS[0] == ("or", 0, 6)
    for x in range(512):
        assert evaluate(WITNESS, x) == target(x)


def evaluate(gates, x):
    wires = [bool(x & (1 << i)) for i in range(9)]
    for op, a, b in gates:
        if op == "not":
            wires.append(not wires[a])
        elif op == "and":
            wires.append(wires[a] and wires[b])
        else:
            assert op == "or"
            wires.append(wires[a] or wires[b])
    return wires[-1]


class Formula:
    def __init__(self):
        self.count = 0
        self.clauses = []
        self.groups = []

    def new(self):
        self.count += 1
        return self.count

    def clause(self, *lits):
        self.clauses.append(" ".join(map(str, lits)) + " 0\n")

    def choice(self, n):
        bits = [self.new() for _ in range(n)]
        self.clause(*bits)
        for a, b in combinations(bits, 2):
            self.clause(-a, -b)
        return bits

    def write(self, path):
        with path.open("w") as output:
            output.write(f"p cnf {self.count} {len(self.clauses)}\n")
            output.writelines(self.clauses)

    def decode(self, model):
        enabled = set(model)
        gates = [("or", 0, 6)]
        for op, left, right in self.groups:
            chosen = [[i for i, v in enumerate(choices) if v in enabled] for choices in (op, left, right)]
            assert all(len(group) == 1 for group in chosen)
            gates.append((("and", "or", "not")[chosen[0][0]], chosen[1][0], chosen[2][0]))
        return gates


def encode(budget, patterns, pin=False, omit=None, live_negation=False):
    f = Formula()
    truth = f.new()
    f.clause(truth)
    groups = f.groups
    for gate in range(1, budget):
        arity = 9 + gate
        op, left, right = f.choice(3), f.choice(arity), f.choice(arity)
        for i in range(arity):
            for j in range(i):
                f.clause(-left[i], -right[j])
            # A NOT repeats its only input in the inert right slot.
            f.clause(-op[2], -left[i], right[i])
        if pin:
            kind, a, b = WITNESS[gate]
            for literal in (op[("and", "or", "not").index(kind)], left[a], right[b]):
                f.clause(literal)
        if omit is not None:
            f.clause(-left[omit])
            f.clause(-right[omit])
        groups.append((op, left, right))

    if live_negation:
        f.clause(*(op[2] for op, _, _ in groups))
        for v in range(9):
            f.clause(*(port[v] for _, left, right in groups for port in (left, right)))

    # Every gate after the prescribed one can lie on a path to the last gate.
    # Shorter solutions can append idempotent ORs. The prescribed gate may be dead.
    for gate in range(len(groups) - 1):
        index = 10 + gate
        uses = [operand[index] for _, left, right in groups[gate + 1:] for operand in (left, right)]
        f.clause(*uses)

    for x in patterns:
        wires = [truth if x & (1 << i) else -truth for i in range(9)]
        wires.append(truth if x & 65 else -truth)
        for op, left, right in groups:
            a, b, out = f.new(), f.new(), f.new()
            for choices, port in ((left, a), (right, b)):
                for selector, wire in zip(choices, wires):
                    f.clause(-selector, -port, wire)
                    f.clause(-selector, port, -wire)
            meet, join, inv = op
            for clause in ((-meet, -out, a), (-meet, -out, b), (-meet, out, -a, -b),
                           (-join, out, -a), (-join, out, -b), (-join, -out, a, b),
                           (-inv, out, a), (-inv, -out, -a)):
                f.clause(*clause)
            wires.append(out)
        f.clause(wires[-1] if target(x) else -wires[-1])
    return f


def boundary():
    minimal = [(1 << a) | (1 << b) for a, b in EDGES]
    maximal = [x for x in range(512) if not target(x) and all(
        x & (1 << v) or target(x | (1 << v)) for v in range(9))]
    return minimal + maximal


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--gates", type=int, default=15, choices=range(2, 17))
    parser.add_argument("--rows", choices=("boundary", "all", "collision"), default="all")
    parser.add_argument("--omit", type=int, choices=(0, 6))
    parser.add_argument("--pin-witness", action="store_true")
    parser.add_argument("--negation-branch", action="store_true",
                        help="require a NOT and a later use of each of the nine original inputs")
    args = parser.parse_args()
    if args.pin_witness and args.gates != 16:
        parser.error("the witness has sixteen gates")
    if args.negation_branch and (args.pin_witness or args.omit is not None):
        parser.error("the negation branch requires all inputs and has no pinned monotone witness")
    check_witness()
    if args.rows == "boundary":
        patterns = boundary()
    elif args.rows == "collision":
        if args.omit is None:
            parser.error("collision rows require --omit")
        patterns = (80, 81) if args.omit == 0 else (257, 321)
    else:
        patterns = range(512)
    formula = encode(args.gates, patterns, pin=args.pin_witness, omit=args.omit,
                     live_negation=args.negation_branch)
    formula.write(args.output)
    print(f"{len(patterns)} inputs, {formula.count} variables, {len(formula.clauses)} clauses")


if __name__ == "__main__":
    main()
