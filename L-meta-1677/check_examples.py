"""Evaluate the prescribed sixteen-gate circuit and a ten-gate boundary counterexample."""
from fixed_first import EDGES, WITNESS, boundary, check_witness, evaluate, target


BOUNDARY_CIRCUIT = (("or", 0, 6), ("or", 1, 9), ("and", 7, 10), ("or", 0, 4),
                    ("and", 2, 12), ("or", 1, 3), ("and", 5, 14), ("or", 11, 13),
                    ("or", 15, 16), ("not", 17, 17))


if __name__ == "__main__":
    check_witness()
    rows = boundary()
    assert len(EDGES) == 12 and len(set(rows)) == 24
    assert len(BOUNDARY_CIRCUIT) == 10 and BOUNDARY_CIRCUIT[0] == WITNESS[0]
    assert all(evaluate(BOUNDARY_CIRCUIT, x) == target(x) for x in rows)
    failures = [x for x in range(512) if evaluate(BOUNDARY_CIRCUIT, x) != target(x)]
    assert failures[0] == 0
    for v, before, after in ((0, 80, 81), (6, 257, 321)):
        assert (before ^ after) == (1 << v) and (before & 65) and (after & 65)
        assert not target(before) and target(after)
    print(f"The 16-gate circuit passes all 512 inputs. The 10-gate circuit passes all {len(rows)} extremal")
    print(f"inputs and fails on {len(failures)} of the 512 inputs, including the empty input.")
    print("Both pairs of inputs prove the prescribed OR's operands must be read again.")
