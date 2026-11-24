"""The edge function of the ten-cycle takes exactly 14 binary AND/OR gates.

This finite case of PEqualNP L-meta-3503 allows unrestricted fan-out and gates
in any topological order. Number the vertices consecutively around the cycle.
For each even vertex, OR its two neighbors and AND that result with the vertex.
Four more OR gates combine the five terms. This is a separated circuit.

Two exhaustive searches rule out every circuit of size at most 13. The C++
search evaluates each wire on the ten minimal positive inputs and the maximal
negative inputs. Those rows determine the output of a monotone circuit. The
Python search stores full truth tables. Both searches allow a computed wire
to remain available to any later gate. The C++ run uses direct search.

Run with Python 3.10+ and a C++17 compiler from this research repository:
    python3 -B L-meta-3503/check_cycle10.py

The universal statement for all bipartite graphs without four-cycles is open.
"""

from pathlib import Path
import subprocess
import sys
import tempfile


SEARCH_DIR = Path(__file__).resolve().parents[1] / "L-meta-612"
sys.path.insert(0, str(SEARCH_DIR))
from verify_three import reaches
from verify_controls import check


def check_star_circuit(edges):
    for assignment in range(1 << 10):
        selected = [(assignment >> i) & 1 for i in range(10)]
        terms = [selected[i] & (selected[(i - 1) % 10] | selected[(i + 1) % 10])
                 for i in range(0, 10, 2)]
        assert any(terms) == any(selected[u] and selected[v] for u, v in edges)


def main():
    edges = [(i, (i + 1) % 10) for i in range(10)]
    check_star_circuit(edges)
    print("Separated 14-gate construction agrees on all 1024 inputs.", flush=True)
    assert not reaches(10, edges, 13)
    print("Python full-truth-table search excludes every circuit of size at most 13.", flush=True)

    # The search interface takes graph ID, vertices, edges and vertex-cover
    # size, followed by pairs of endpoints. Five alternating vertices cover
    # every edge, and five disjoint edges force any cover to use at least five.
    row = [0, 10, 10, 5, *(vertex for edge in edges for vertex in edge)]
    graph_input = " ".join(map(str, row)) + "\n"
    with tempfile.TemporaryDirectory() as scratch:
        binary = Path(scratch) / "search"
        subprocess.run(["c++", "-O3", "-std=c++17", SEARCH_DIR / "kernel_search.cpp",
                        "-o", binary], check=True)
        for offset, budget, verdict in ((0, 13, "NONE"), (1, 14, "FOUND")):
            run = subprocess.run([binary, "0", "0", str(offset), "--direct", "16"],
                                 input=graph_input, capture_output=True, text=True, check=True)
            header, *trace = run.stdout.splitlines()
            expected = f"kernel 0 n 10 edges 10 budget {budget} {verdict} states"
            assert header.startswith(expected + " ") and header.split()[-1].isdigit()
            if verdict == "FOUND":
                assert len(trace) == budget
                check((10, edges), budget, trace)
            print(header)


if __name__ == "__main__":
    main()
