"""Search a fan-in-two AND/OR circuit of a given gate budget against the exact affine tests."""
import argparse
import json
import shutil
import signal
import subprocess
import tempfile
from pathlib import Path

from affine_benchmark import benchmark, incidence, reference_circuits


def search(q, budget, solver, seconds, pin_star=False, output=None):
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder)
        masks = path / 'rows.json'
        benchmark(q, test_path=masks)
        rows = json.loads(masks.read_text())
        inputs = rows['input_bits']
        cases = [(mask, True) for mask in rows['positive_masks']]
        cases.extend((mask, False) for mask in rows['negative_masks'])
        variables = clauses = 0
        gates = []
        cnf_body = path / 'clauses'
        with cnf_body.open('w') as stream:
            def fresh():
                nonlocal variables
                variables += 1
                return variables

            def clause(*literals):
                nonlocal clauses
                clauses += 1
                stream.write(' '.join(map(str, literals)) + ' 0\n')

            def select(count):
                # One or more selectors may be true. Their wires must agree on all
                # test rows, so retaining the first true selector gives the same circuit values.
                choices = [fresh() for _ in range(count)]
                clause(*choices)
                return choices

            star = reference_circuits(incidence(q))[0] if pin_star else None
            if star and len(star['gates']) != budget:
                raise ValueError('Pinning the star requires its exact gate count')
            for j in range(budget):
                count = inputs + j
                left, right = select(count), select(count)
                is_and = fresh()
                values = []
                for i in range(count):
                    for k in range(i):
                        clause(-left[i], -right[k])
                if star:
                    g = star['gates'][j]
                    a, b = sorted(g['inputs'])
                    clause(left[a])
                    clause(right[b])
                    clause(is_and if g['op'] == 'and' else -is_and)
                for row, (mask, truth) in enumerate(cases):
                    a, b, y = fresh(), fresh(), fresh()
                    for side, wire in ((left, a), (right, b)):
                        for i, choice in enumerate(side):
                            if i < inputs:
                                clause(-choice, wire if (mask >> i) & 1 else -wire)
                            else:
                                old = gates[i-inputs][3][row]
                                clause(-choice, -wire, old)
                                clause(-choice, wire, -old)
                    clause(-is_and, -y, a)
                    clause(-is_and, -y, b)
                    clause(-is_and, y, -a, -b)
                    clause(is_and, y, -a)
                    clause(is_and, y, -b)
                    clause(is_and, -y, a, b)
                    values.append(y)
                    if j == budget-1:
                        clause(y if truth else -y)
                gates.append((left, right, is_and, values))

        cnf = path / 'circuit.cnf'
        with cnf.open('wb') as dst, cnf_body.open('rb') as src:
            dst.write(f'p cnf {variables} {clauses}\n'.encode())
            shutil.copyfileobj(src, dst)
        run = subprocess.run([solver, '-q', '-t', str(seconds), str(cnf)], capture_output=True, text=True)
        status = {0: 'UNKNOWN', -signal.SIGALRM: 'UNKNOWN (time limit)',
                  10: 'SAT', 20: 'UNSAT'}.get(run.returncode)
        if status is None:
            raise RuntimeError(f'Solver exit {run.returncode}: {run.stderr} {run.stdout[:300]}')
        print(f'q={q} gates={budget} pinned={pin_star} rows={len(cases)} variables={variables} clauses={clauses} {status}')
        if status == 'SAT':
            model = {int(lit) for line in run.stdout.splitlines() if line.startswith('v ')
                     for lit in line.split()[1:] if int(lit) > 0}
            def source(choices):
                return next(i for i, selector in enumerate(choices) if selector in model)
            result = {'output': inputs+budget-1, 'gates': [
                {'op': 'and' if op in model else 'or', 'inputs': [source(l), source(r)]}
                for l, r, op, _ in gates]}
            check = benchmark(q, candidate=result)['circuits']['candidate']
            if check['false_positive'] or check['false_negative']:
                raise RuntimeError('Decoded candidate failed the exhaustive truth table')
            print('Decoded candidate passed exhaustive verification.')
            if output:
                output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--q', type=int, choices=[2, 3], required=True)
    p.add_argument('--gates', type=int, required=True)
    p.add_argument('--solver', default='cadical')
    p.add_argument('--seconds', type=int, default=120)
    p.add_argument('--pin-star', action='store_true')
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    if a.gates < 1 or a.seconds < 1:
        p.error('Gates and seconds must be positive')
    search(a.q, a.gates, a.solver, a.seconds, a.pin_star, a.output)
