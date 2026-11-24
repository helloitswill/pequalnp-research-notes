"""Exhaustive benchmark for the full edge function of the order-2 and order-3 biaffine planes.

Run with python3 affine_benchmark.py, or test a circuit with --q 3 --circuit circuit.json.
JSON follows the project wire numbering: {"gates":[{"op":"and","inputs":[0,9]}],"output":18}.
Point (x,y) has wire q*x+y. Line y=a*x+b has wire q*q+q*a+b. A gate writes the next wire.
"""

import argparse
import json
from collections import deque
from pathlib import Path


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def incidence(q):
    return [sum(1 << (q*a + (y-a*x) % q) for a in range(q))
            for x in range(q) for y in range(q)]


def graph_girth(rows):
    m = len(rows)
    graph = [[] for _ in range(2*m)]
    for p, row in enumerate(rows):
        for line in indices(row):
            graph[p].append(m+line)
            graph[m+line].append(p)
    best = None
    for start in range(2*m):
        distances = {start: 0}
        parents = {start: None}
        queue = deque([start])
        while queue:
            v = queue.popleft()
            for w in graph[v]:
                if w not in distances:
                    distances[w] = distances[v]+1
                    parents[w] = v
                    queue.append(w)
                elif parents[v] != w:
                    length = distances[v]+distances[w]+1
                    best = length if best is None else min(best, length)
    return best


def reference_circuits(rows):
    m = len(rows)

    def make_circuit(representative):
        gates = []

        def combine(op, wires):
            wires = list(wires)
            if not wires:
                gates.append({"op": op, "inputs": []})
                return 2*m + len(gates)-1
            wire = wires[0]
            for other in wires[1:]:
                gates.append({"op": op, "inputs": [wire, other]})
                wire = 2*m + len(gates)-1
            return wire

        if not representative:
            terms = [combine("and", [p, combine("or", (m+l for l in indices(row)))])
                     for p, row in enumerate(rows)]
            output = combine("or", terms)
        else:
            # The clause for a nonincident (p,l) rejects that one-hot pair.
            # Several active vertices on a shore can satisfy every exclusion clause.
            other_points = [combine("or", (t for t in range(m) if t != p)) for p in range(m)]
            other_lines = [combine("or", (m+t for t in range(m) if t != l)) for l in range(m)]
            clauses = [combine("or", range(m)), combine("or", range(m, 2*m))]
            for p, row in enumerate(rows):
                for l in range(m):
                    if not (row >> l) & 1:
                        clauses.append(combine("or", [other_points[p], other_lines[l]]))
            output = combine("and", clauses)
        return {"gates": gates, "output": output}

    return make_circuit(False), make_circuit(True)


def decode(circuit):
    def nat(i):
        return type(i) is int and i >= 0

    gates = []
    for gate in circuit["gates"]:
        op, args = gate["op"], gate["inputs"]
        if op not in ("and", "or") or not isinstance(args, list) or len(args) > 2 or not all(map(nat, args)):
            raise ValueError("Each gate must be AND or OR with at most two natural-number inputs")
        gates.append((op, args))
    if not nat(circuit["output"]):
        raise ValueError("The output wire must be a natural number")
    return gates, circuit["output"]


def evaluate(gates, output, inputs, universe):
    # One Python bit per line subset. Missing and forward wires evaluate to false (project semantics).
    wires = inputs.copy()
    for op, args in gates:
        value = universe if op == "and" else 0
        for index in args:
            operand = wires[index] if index < len(wires) else 0
            value = (value & operand) if op == "and" else (value | operand)
        wires.append(value)
    return wires[output] if output < len(wires) else 0


def benchmark(q, candidate=None, test_path=None):
    rows = incidence(q)
    m = q*q
    subsets = 1 << m
    universe = (1 << subsets)-1
    line_bits = [sum(1 << s for s in range(subsets) if s >> l & 1) for l in range(m)]
    edges = sum(row.bit_count() for row in rows)
    assert edges == q**3 and all(row.bit_count() == q for row in rows)
    assert all(sum(row >> l & 1 for row in rows) == q for l in range(m))
    girth = graph_girth(rows)
    assert girth == (8 if q == 2 else 6)

    star, one_hot = reference_circuits(rows)
    assert len(star["gates"]) == q**3 + q*q - 1
    circuits = {"star": star, "one_hot_comparison": one_hot}
    if candidate is not None:
        circuits["candidate"] = candidate
    programs = {name: decode(c) for name, c in circuits.items()}
    results = {name: {"gates": len(program[0]), "false_positive": 0, "false_negative": 0,
                      "one_hot_errors": 0, "certificate_errors": 0} for name, program in programs.items()}
    positive_rows = [(1 << p) | (1 << (m+l)) for p, row in enumerate(rows) for l in indices(row)]
    negative_rows = []
    negatives = maximal = 0
    for points in range(subsets):
        neighbors = 0
        for p in indices(points):
            neighbors |= rows[p]
        allowed = (subsets-1) ^ neighbors
        # All lines avoiding these points must be present in a maximal independent set.
        # Every omitted point must then hit one of those lines.
        is_maximal = all((points >> p & 1) or (row & allowed) for p, row in enumerate(rows))
        maximal += is_maximal
        if is_maximal:
            negative_rows.append(points | (allowed << m))
        negatives += 1 << allowed.bit_count()
        expected = 0
        for l in indices(neighbors):
            expected |= line_bits[l]
        inputs = [universe if points >> p & 1 else 0 for p in range(m)] + line_bits
        for name, (gates, output) in programs.items():
            result = results[name]
            actual = evaluate(gates, output, inputs, universe)
            fp, fn = actual & ~expected, expected & ~actual
            result["false_positive"] += fp.bit_count()
            result["false_negative"] += fn.bit_count()
            if fp and "first_false_positive" not in result:
                line_set = (fp & -fp).bit_length()-1
                result["first_false_positive"] = {"points": [divmod(p,q) for p in indices(points)],
                                                   "lines_ab": [divmod(l,q) for l in indices(line_set)]}
            if points.bit_count() == 1:
                result["one_hot_errors"] += sum((fp | fn) >> (1 << l) & 1 for l in range(m))
                result["certificate_errors"] += sum(fn >> (1 << l) & 1 for l in indices(neighbors))
            result["certificate_errors"] += int(bool(is_maximal and (actual >> allowed & 1)))
    for result in results.values():
        assert (result["certificate_errors"] == 0) == (result["false_positive"] + result["false_negative"] == 0)
    assert results["star"]["certificate_errors"] == 0
    assert results["one_hot_comparison"]["one_hot_errors"] == 0 < results["one_hot_comparison"]["false_positive"]
    if test_path is not None:
        test_path.write_text(json.dumps({"q": q, "input_bits": 2*m, "positive_masks": positive_rows,
                                         "negative_masks": negative_rows}, indent=2) + "\n")
    return {"q": q, "vertices": 2*m, "edges": edges, "girth": girth, "full_inputs": subsets**2,
            "independent_inputs": negatives, "maximal_independent_inputs": maximal,
            "exact_monotone_test_rows": edges + maximal, "circuits": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--q", type=int, choices=[2,3])
    parser.add_argument("--circuit", type=Path)
    parser.add_argument("--write-tests", type=Path, help="Write the exact monotone test rows as input bit masks")
    args = parser.parse_args()
    if (args.circuit or args.write_tests) and args.q is None:
        parser.error("--circuit and --write-tests require --q")
    candidate = json.loads(args.circuit.read_text()) if args.circuit else None
    reports = [benchmark(q, candidate, args.write_tests) for q in ([args.q] if args.q else [2,3])]
    print(json.dumps(reports, indent=2))
    if candidate is not None:
        raise SystemExit(int(reports[0]["circuits"]["candidate"]["certificate_errors"] != 0))
