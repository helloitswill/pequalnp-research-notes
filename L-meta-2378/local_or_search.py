"""Exact search for local sound gadgets with a bounded number of OR gates.

With --proof FILE, save DIMACS next to the textual LRAT proof and verify the
unit-propagation trace. Use the default Python interpreter without -O.
"""
import argparse
import itertools
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


def graph(name):
    if name.startswith('theta'):
        size, edges = 2, []
        for length in map(int, name[5:]):
            path = [0, *range(size, size + length - 1), 1]
            size += length - 1
            edges.extend(zip(path, path[1:]))
        return size, edges
    if name.startswith('c'):
        size = int(name[1:])
        return size, [(i, (i + 1) % size) for i in range(size)]
    if name == 'fano':
        return 14, [(i, 7 + (i + a) % 7) for i in range(7) for a in (0, 1, 3)]
    if name == 'K4sub':
        edges = []
        for midpoint, (a, b) in enumerate(itertools.combinations(range(4), 2), 4):
            edges.extend([(a, midpoint), (b, midpoint)])
        return 10, edges
    if name == 'K23':
        return 5, list(itertools.product(range(2), range(2, 5)))
    raise ValueError('Use c6, c8, theta333, theta244, K4sub, fano or K23')


def neighbors(size, edges):
    rows = [set() for _ in range(size)]
    for a, b in edges:
        rows[a].add(b)
        rows[b].add(a)
    return rows


def graph_automorphisms(size, edges):
    rows = neighbors(size, edges)
    permutation, used = [-1] * size, set()

    def options(x):
        return [y for y in range(size) if y not in used and len(rows[x]) == len(rows[y])
                and all((z in rows[x]) == (w in rows[y])
                        for z, w in enumerate(permutation) if w >= 0)]

    def generate():
        if len(used) == size:
            yield tuple(permutation)
            return
        remaining = [(v, options(v)) for v in range(size) if permutation[v] < 0]
        vertex, choices = min(remaining, key=lambda item: (len(item[1]), item[0]))
        for target in choices:
            permutation[vertex] = target
            used.add(target)
            yield from generate()
            used.remove(target)
            permutation[vertex] = -1

    return list(generate())


def forest_or_checked_cycle(size, edges):
    rows = neighbors(size, edges)
    while any(len(row) == 1 for row in rows):
        vertex = next(i for i, row in enumerate(rows) if len(row) == 1)
        rows[rows[vertex].pop()].remove(vertex)
    core = {i for i, row in enumerate(rows) if row}
    if not core:
        return True
    reached, pending = set(), [next(iter(core))]
    while pending:
        vertex = pending.pop()
        if vertex not in reached:
            reached.add(vertex)
            pending.extend(rows[vertex] - reached)
    return reached == core and len(core) in (6, 8) and all(len(rows[v]) == 2 for v in core)


class Encoder:
    def __init__(self, size, edges):
        self.size = size
        self.edges = edges
        self.positive = [(1 << a) | (1 << b) for a, b in edges]
        self.rows = self.positive + [
            m for m in range(1 << size) if not self.truth(m)
            and all(self.truth(m | (1 << v)) for v in range(size) if not m >> v & 1)]
        self.gates, self.clauses, self.nvars = [], [], 0

    def truth(self, mask):
        return any(mask & edge == edge for edge in self.positive)

    def fresh(self):
        self.nvars += 1
        return self.nvars

    def emit(self, *literals):
        self.clauses.append(literals)

    def arm(self):
        n, j = self.size, len(self.gates)
        use = [self.fresh() for _ in range(n + j)]
        disabled = self.fresh()
        edges = set(self.positive)
        # A term with more than two raw variables or a nonedge raw pair cannot
        # help accept any edge. Replacing it by false only shrinks its output.
        for a, b in itertools.combinations(range(n), 2):
            if (1 << a | 1 << b) not in edges:
                self.emit(-use[a], -use[b])
        for a, b, c in itertools.combinations(range(n), 3):
            if {1 << a | 1 << b, 1 << a | 1 << c, 1 << b | 1 << c} <= edges:
                self.emit(-use[a], -use[b], -use[c])
        values = []
        for r, mask in enumerate(self.rows):
            val = self.fresh()
            values.append(val)
            if r < len(self.positive):
                # A certificate of truth requires all selected wires to be true.
                self.emit(-val, -disabled)
                for i in range(n):
                    if not mask >> i & 1:
                        self.emit(-val, -use[i])
                for i, gate in enumerate(self.gates):
                    self.emit(-val, -use[n + i], gate[2][r])
            else:
                # A certificate of falsity requires a selected false wire.
                explanations = [disabled] + [use[i] for i in range(n) if not mask >> i & 1]
                for i, gate in enumerate(self.gates):
                    bad = self.fresh()
                    self.emit(-bad, use[n + i])
                    self.emit(-bad, -gate[2][r])
                    explanations.append(bad)
                self.emit(val, *explanations)
        return use, disabled, values

    def ordered(self, left, right, exceptions=()):
        prefix = []
        for a, b in zip(left, right):
            self.emit(*exceptions, *[-var for var in prefix], -a, b)
            equal = self.fresh()
            self.emit(-a, -b, equal)
            self.emit(a, b, equal)
            prefix.append(equal)

    def canonical_first(self, left, right):
        n = self.size
        terms = [1 << i for i in range(n)] + self.positive
        def good(m):
            return {i for i, edge in enumerate(self.positive) if edge & m == m}
        def key(m):
            return tuple(m >> i & 1 for i in range(n))
        def canonical(a, b):
            return (a, b) if key(a) < key(b) else (b, a)
        remaining = {canonical(a, b) for a, b in itertools.combinations(terms, 2)
                     if good(a) - good(b) and good(b) - good(a)}
        group = graph_automorphisms(n, self.edges)
        choices = []
        while remaining:
            a, b = min(remaining)
            for perm in group:
                def image(m):
                    return sum(1 << perm[i] for i in range(n) if m >> i & 1)
                remaining.discard(canonical(image(a), image(b)))
            choice = self.fresh()
            choices.append(choice)
            for arm, mask in [(left, a), (right, b)]:
                self.emit(-choice, -arm[1])
                for i, select in enumerate(arm[0]):
                    self.emit(-choice, select if mask >> i & 1 else -select)
        self.emit(*choices)

    def add_or(self, symmetry):
        j = len(self.gates)
        left, right = self.arm(), self.arm()
        output = [self.fresh() for _ in self.rows]
        for i, val in enumerate(output):
            if i < len(self.positive):
                self.emit(-val, left[2][i], right[2][i])
            else:
                self.emit(-left[2][i], val)
                self.emit(-right[2][i], val)
        self.ordered(left[0], right[0])
        if symmetry and j == 0:
            self.canonical_first(left, right)
        if symmetry and j >= 2:
            count = len(self.positive)
            self.ordered(self.gates[-1][2][:count], output[:count], [left[0][-1], right[0][-1]])
        self.gates.append((left, right, output))

    def restriction_bounds(self):
        for vertex in range(self.size):
            remaining = [edge for edge in self.edges if vertex not in edge]
            if not remaining or not forest_or_checked_cycle(self.size, remaining):
                continue
            # Each OR with this raw input in either arm disappears upon erasing
            # the vertex. The retained graph needs |remaining edges|-1 ORs.
            cap = len(self.gates) - (len(remaining) - 1)
            if cap < 0:
                self.emit()
                continue
            touched = [self.fresh() for _ in self.gates]
            for var, (left, right, _) in zip(touched, self.gates):
                self.emit(-left[0][vertex], var)
                self.emit(-right[0][vertex], var)
            for group in itertools.combinations(touched, cap + 1):
                self.emit(*[-var for var in group])

    def require_coverage(self, bits, count):
        previous = []
        for i, bit in enumerate(bits):
            row = [self.fresh() for _ in range(min(count, i + 1))]
            for j, val in enumerate(row):
                keep = [previous[j]] if j < len(previous) else []
                self.emit(-val, *keep, bit)
                if j:
                    self.emit(-val, *keep, previous[j - 1])
            previous = row
        self.emit(previous[count - 1])

    def finish(self, budget, coverage, symmetry, peel_bounds):
        for _ in range(budget):
            self.add_or(symmetry)
        if peel_bounds:
            if coverage != len(self.positive):
                raise ValueError('The restriction bounds require all edges to be accepted')
            self.restriction_bounds()
        self.out = self.arm()
        bits = self.out[2]
        for bit in bits[len(self.positive):]:
            self.emit(-bit)
        if coverage == len(self.positive):
            for bit in bits[:coverage]:
                self.emit(bit)
        else:
            self.require_coverage(bits[:len(self.positive)], coverage)

    def decode(self, output, coverage):
        selected = {int(x) for line in output.splitlines() if line.startswith('v ')
                    for x in line.split()[1:] if int(x) > 0}
        def term(arm):
            return None if arm[1] in selected else [i for i, var in enumerate(arm[0]) if var in selected]
        gates = [(term(a), term(b)) for a, b, _ in self.gates]
        out = term(self.out)
        def evaluate(mask):
            wires = [bool(mask >> i & 1) for i in range(self.size)]
            def meet(indices):
                return indices is not None and all(wires[i] for i in indices)
            for a, b in gates:
                wires.append(meet(a) or meet(b))
            return meet(out)
        accepted = [edge for edge, mask in zip(self.edges, self.positive) if evaluate(mask)]
        if len(accepted) < coverage or any(evaluate(mask) and not self.truth(mask) for mask in range(1 << self.size)):
            raise ValueError('Decoded circuit failed the independent full truth table')
        return dict(n=self.size, edges=self.edges, accepted=accepted, gates=gates, out=out)


def verify(cnf, proof):
    clauses = {}
    with cnf.open() as source:
        for line in source:
            if not line.strip() or line.startswith(('p', 'c')):
                continue
            numbers = [int(x) for x in line.split()]
            assert numbers.pop() == 0
            clauses[len(clauses) + 1] = numbers
    last = len(clauses)
    checked = 0
    with proof.open() as stream:
        for raw in stream:
            pieces = raw.split()
            if len(pieces) > 1 and pieces[1] == 'd':
                assert pieces[-1] == '0'
                for ref in pieces[2:-1]:
                    del clauses[int(ref)]
                continue
            row = [int(x) for x in pieces]
            end = row.index(0, 1)
            label = row[0]
            literals = row[1:end]
            hints = row[end + 1:-1]
            assert row[-1] == 0 and label > last and hints
            last = label
            true = {-x for x in literals}
            assert not any(-x in true for x in true)
            for j, hint in enumerate(hints):
                assert hint > 0
                clause=clauses[hint]
                assert not any(x in true for x in clause)
                available = [x for x in clause if -x not in true]
                if j + 1 == len(hints):
                    assert not available
                else:
                    assert len(available) == 1
                    true.add(available[0])
            checked += 1
            if not literals:
                print('Verified empty clause after', checked, 'RUP derivations')
                return
            clauses[label] = literals
    raise ValueError('Proof ended before deriving an empty clause')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('graph')
    parser.add_argument('budget', type=int)
    parser.add_argument('--cover', type=int, help='minimum number of edge pairs to accept')
    parser.add_argument('--sym', action='store_true', help='break graph and independent-gate ordering symmetries')
    parser.add_argument('--peel-bounds', action='store_true', help='use proven C6/C8 and forest restriction bounds')
    parser.add_argument('--seconds', type=int, default=120)
    parser.add_argument('--solver', default='cadical')
    parser.add_argument('--proof', type=Path, help='save DIMACS and independently check a returned LRAT proof')
    parser.add_argument('--candidate', type=Path, help='save a decoded fully tested SAT witness')
    parser.add_argument('--dimacs', type=Path, help='export the instance without running a solver')
    args = parser.parse_args()
    size, edges = graph(args.graph)
    coverage = len(edges) if args.cover is None else args.cover
    if args.budget < 0 or not 1 <= coverage <= len(edges):
        parser.error('The budget must be nonnegative and coverage between one and the number of edges')
    if args.sym and (coverage < 2 or not args.budget):
        parser.error('First-gate symmetry requires at least two accepted edges and a positive budget')
    enc = Encoder(size, edges)
    enc.finish(args.budget, coverage, args.sym, args.peel_bounds)
    with tempfile.TemporaryDirectory() as folder:
        cnf = args.dimacs or Path(folder)/'instance.cnf'
        with cnf.open('w') as f:
            f.write(f'p cnf {enc.nvars} {len(enc.clauses)}\n')
            for row in enc.clauses:
                f.write(' '.join(map(str, row)) + ' 0\n')
        if args.dimacs:
            return
        command = [args.solver, '-q', '-t', str(args.seconds)]
        if args.proof:
            args.proof.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(cnf, args.proof.with_suffix('.cnf'))
            command.extend(['--lrat', '--no-binary', str(cnf), str(args.proof)])
        else:
            command.append(str(cnf))
        run = subprocess.run(command, capture_output=True, text=True)
        label = {10: 'SAT', 20: 'UNSAT', 0: 'UNKNOWN', -14: 'UNKNOWN'}.get(run.returncode)
        if label is None:
            raise RuntimeError(f'Solver exit {run.returncode}: {run.stderr}')
        print(f'{args.graph} OR gates={args.budget} required edges={coverage} '
              f'boundary rows={len(enc.rows)} variables={enc.nvars} clauses={len(enc.clauses)} {label}')
        if run.returncode == 20 and args.proof:
            if not __debug__:
                raise RuntimeError('LRAT assertions require Python without -O')
            verify(cnf, args.proof)
        if run.returncode == 10:
            candidate = enc.decode(run.stdout, coverage)
            print('Fully checked accepted edges:', candidate['accepted'])
            if args.candidate:
                args.candidate.write_text(json.dumps(candidate, indent=2) + '\n')


if __name__ == '__main__':
    main()
