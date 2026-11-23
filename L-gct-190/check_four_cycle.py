"""Verify row weights and the fixed-column coefficient identities in FourRowCycle.md."""
from itertools import combinations, permutations, product
from math import prod


def phase_sum(exponents):
    counts = [0, 0, 0, 0]
    for rows in permutations(range(4), len(exponents)):
        power = sum(r * e for r, e in zip(rows, exponents))
        counts[power % 4] += 1
    assert counts[1] == counts[3]
    return counts[0] - counts[2]


expected = {
    (1, 1, 1, 1): -24,
    (3, 3, 3, 3): -24,
    (2, 2): -4,
    (2, 2, 2, 2): 24,
    (1, 3): -4,
    (1, 1, 3, 3): 8,
    (1, 1, 2): 8,
    (3, 3, 2): 8,
}
for modes, answer in expected.items():
    assert phase_sum(modes) == answer


def coeff(matrices, rows, columns):
    """Coefficient of the product of distinct scalar variables at the all-ones matrix."""
    answer = 0
    for order in permutations(columns):
        for picks in permutations(range(len(rows)), len(matrices)):
            answer += prod(matrix[rows[pos]][order[pos]] for pos, matrix in zip(picks, matrices))
    return answer


indices = tuple(range(5))
bottom = tuple(range(4))
top = 4
pairs_checked = 0
for j in indices:
    fixed = [[(int(col == j) * (-4 if row == top else 1))
              for col in indices] for row in indices]
    outside = set(indices) - {j}
    for a, b in product(indices, repeat=2):
        # Polarize in the two copies of h and check each basis pair separately.
        def even(col):
            return [[int(row != top and k == col) * (-1)**row for k in indices]
                    for row in indices]
        factors = [fixed, even(a), even(b)]
        pair_outside = a != b and {a, b}.issubset(outside)
        assert coeff(factors, indices, indices) == (16 if pair_outside else 0)
        for k in outside:
            columns = tuple(c for c in indices if c != k)
            allowed = pair_outside and k not in (a, b)
            assert coeff(factors, bottom, columns) == (-8 if allowed else 0)
        pairs_checked += 1
print(f"Verified {len(expected)} row phases and {pairs_checked} polarized column cases.")
