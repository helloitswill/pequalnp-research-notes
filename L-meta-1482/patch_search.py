"""Search budget-neutral replacements for selected line stars in PG(2,3)."""

import argparse
import json
from itertools import combinations
from pathlib import Path
import subprocess
import tempfile


def patch(lines):
    """Group points with identical incidences in the selected lines into one OR."""
    groups = {}
    for p in range(13):
        signature = tuple(i for i, line in enumerate(lines) if (p - line) % 13 in (0, 1, 3, 9))
        if signature:
            groups.setdefault(signature, []).append(p)
    signatures = list(groups)
    points = list(groups.values())
    edges = [(i, len(points) + j) for i, sig in enumerate(signatures) for j in sig]
    inputs = len(points) + len(lines)
    cost = 5 * len(lines) - 1 - sum(len(group) - 1 for group in points)
    return points, edges, inputs, cost


def target(mask, edges):
    return any(mask >> i & 1 and mask >> j & 1 for i, j in edges)


def marking(gates, n, marked, varying):
    ordinary = [v == marked for v in range(n)]
    marks = [v == varying for v in range(n)]
    for op, i, j in gates:
        if op == 'and':
            marks.append((ordinary[i] and marks[j]) or (marks[i] and ordinary[j]))
            ordinary.append(ordinary[i] and ordinary[j])
        else:
            marks.append(marks[i] or marks[j])
            ordinary.append(ordinary[i] or ordinary[j])
    return marks[-1]


def verifies(gates, n, edges, marked, require_double):
    for mask in range(1 << n):
        wires = [bool(mask >> i & 1) for i in range(n)]
        for op, i, j in gates:
            if not 0 <= i < j < len(wires):
                return False
            wires.append((wires[i] and wires[j]) if op == 'and' else (wires[i] or wires[j]))
        if wires[-1] != target(mask, edges):
            return False
    p, line = marked
    return not require_double or not (marking(gates, n, p, line) or marking(gates, n, line, p))


class Formula:
    def __init__(self):
        self.variables = 1
        self.clauses = [(1,)]

    def fresh(self):
        self.variables += 1
        return self.variables

    def clause(self, *lits):
        if 1 in lits:
            return
        self.clauses.append(tuple(x for x in lits if x != -1))

    def choose(self, n):
        choices = [self.fresh() for _ in range(n)]
        self.clause(*choices)
        for a, b in combinations(choices, 2):
            self.clause(-a, -b)
        return choices

    def selected(self, choices, values):
        y = self.fresh()
        for flag, v in zip(choices, values):
            self.clause(-flag, -y, v)
            self.clause(-flag, y, -v)
        return y

    def conjunction(self, a, b):
        y = self.fresh()
        self.clause(-y, a)
        self.clause(-y, b)
        self.clause(y, -a, -b)
        return y

    def disjunction(self, a, b):
        return -self.conjunction(-a, -b)

    def conditional(self, flag, a, b):
        y = self.fresh()
        self.clause(-flag, -a, y)
        self.clause(-flag, a, -y)
        self.clause(flag, -b, y)
        self.clause(flag, b, -y)
        return y

    def gate(self, flag, a, b):
        y = self.fresh()
        self.clause(-flag, -y, a)
        self.clause(-flag, -y, b)
        self.clause(-flag, y, -a, -b)
        self.clause(flag, y, -a)
        self.clause(flag, y, -b)
        self.clause(flag, -y, a, b)
        return y


def synthesize(n, edges, marked, budget, require_double, seconds, solver, connected=False):
    p, line = marked
    cases = {(1 << a) | (1 << b) for a, b in edges}
    for mask in range(1 << n):
        if not target(mask, edges) and all(mask >> i & 1 or target(mask | 1 << i, edges) for i in range(n)):
            cases.add(mask)
    cases.update([1 << p, 1 << line])
    rows = {mask: [1 if mask >> i & 1 else -1 for i in range(n)] for mask in sorted(cases)}
    marks = {point: rows[1 << other].copy() for point, other in ((p, line), (line, p))}
    cnf = Formula()
    gates = []
    for j in range(budget):
        left = cnf.choose(n + j)
        right = cnf.choose(n + j)
        for a, u in enumerate(left):
            for v in right[:a+1]:
                cnf.clause(-u, -v)
        # Choose the lexicographically least topological ordering of the internal
        # gates. An adjacent inversion in the larger operand can always be swapped:
        # the second gate then cannot read the first one's output. Keep the output
        # gate fixed in the last position, also for circuits padded with dead gates.
        if gates and j + 1 < budget:
            _, previous_left, previous_right = gates[-1]
            for i, old_max in enumerate(previous_right):
                for new_max in right[:i]:
                    cnf.clause(-old_max, -new_max)
                for old_min, old_flag in enumerate(previous_left[:i]):
                    for new_flag in left[:old_min]:
                        cnf.clause(-old_max, -right[i], -old_flag, -new_flag)
        op = cnf.fresh()
        gates.append((op, left, right))
        operands = {}
        for mask, values in rows.items():
            a, b = cnf.selected(left, values), cnf.selected(right, values)
            operands[mask] = (a, b)
            values.append(cnf.gate(op, a, b))
        if require_double:
            for singleton, values in marks.items():
                x, y = operands[1 << singleton]
                a, b = cnf.selected(left, values), cnf.selected(right, values)
                product = cnf.disjunction(cnf.conjunction(x, b), cnf.conjunction(a, y))
                values.append(cnf.conditional(op, product, cnf.disjunction(a, b)))
    for mask, values in rows.items():
        cnf.clause(values[-1] if target(mask, edges) else -values[-1])
    for i in range(n):
        # Every input has a neighbor, so the function depends on it.
        cnf.clause(*(side[i] for _, left, right in gates for side in (left, right)))
    if connected:
        # This search is for the indicated exact gate count. A smallest witness
        # has every gate in its output cone, so the smaller counts can be tested separately.
        for j in range(budget - 1):
            cnf.clause(*(side[n+j] for _, left, right in gates[j+1:] for side in (left, right)))
        if budget > 1:
            cnf.clause(gates[-1][2][-1])
    if require_double:
        for values in marks.values():
            cnf.clause(-values[-1])
    with tempfile.TemporaryDirectory() as folder:
        f = Path(folder) / 'circuit.cnf'
        with f.open('w') as out:
            out.write(f'p cnf {cnf.variables} {len(cnf.clauses)}\n')
            for clause in cnf.clauses:
                out.write(' '.join(map(str, clause)) + ' 0\n')
        try:
            run = subprocess.run([solver, '-q', str(f)], capture_output=True, text=True, timeout=seconds)
        except subprocess.TimeoutExpired:
            return 'TIMEOUT', None
    if run.returncode == 20:
        return 'UNSAT', None
    if run.returncode != 10:
        raise RuntimeError(f'solver returned {run.returncode}: {run.stderr[:300]}')
    model = {int(x) for row in run.stdout.splitlines() if row.startswith('v ') for x in row.split()[1:]}
    def choice(bits):
        picked = [i for i, flag in enumerate(bits) if flag in model]
        if len(picked) != 1:
            raise ValueError('invalid selector assignment')
        return picked[0]
    witness = [('and' if op in model else 'or', choice(a), choice(b)) for op, a, b in gates]
    if not verifies(witness, n, edges, marked, require_double):
        raise ValueError('model failed the independent exhaustive circuit evaluator')
    return 'SAT', witness


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lines', type=int, nargs='+', required=True)
    parser.add_argument('--point', type=int, required=True)
    parser.add_argument('--line', type=int, required=True)
    parser.add_argument('--extra', type=int, default=0)
    parser.add_argument('--control', action='store_true')
    parser.add_argument('--connected', action='store_true')
    parser.add_argument('--seconds', type=int, default=45)
    parser.add_argument('--solver', default=str(Path.home()/'.elan/toolchains/leanprover--lean4---v4.36.0/bin/cadical'))
    args = parser.parse_args()
    points, edges, n, base = patch(args.lines)
    p = next(i for i, group in enumerate(points) if args.point in group)
    line = len(points) + args.lines.index(args.line)
    if (p, line) not in edges:
        parser.error('the marked point and line must be incident')
    budget = base + args.extra
    status, gates = synthesize(n, edges, (p, line), budget, not args.control, args.seconds, args.solver, args.connected)
    print(json.dumps(dict(lines=args.lines, point=args.point, line=args.line, groups=points,
        inputs=n, edges=len(edges), gates=budget, require_double=not args.control,
        connected=args.connected, status=status, witness=gates)))
