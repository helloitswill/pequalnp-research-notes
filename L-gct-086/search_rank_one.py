"""Count flat rank-one lines built from centered multisets of 0 and fourth roots of unity.

Row and column permutations are removed by recording each multiset once.
All arithmetic is integral. The n=4 example is also checked directly over the
24 permutations, independently of the elementary symmetric function formula.
"""
from itertools import permutations
from math import factorial


def elementary(a, b, n):
    """Coefficients of (1 - z²)^a (1 + z²)^b, through degree n."""
    coeff = [1] + [0] * n
    for sign in [-1] * a + [1] * b:
        for k in range(n, 1, -1):
            coeff[k] += sign * coeff[k - 2]
    return coeff


def centered_types(n):
    # a counts ±1 pairs and b counts ±i pairs. Other entries are zero.
    return [(a, b) for a in range(n // 2 + 1)
            for b in range(n // 2 - a + 1) if a + b > 0]


def flat_count(n):
    signatures = [elementary(a, b, n) for a, b in centered_types(n)]
    count = sum(all(x * y == 0 for x, y in zip(row[1:], col[1:]))
                for row in signatures for col in signatures)
    return len(signatures) ** 2, count


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def multiply(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def four_by_four():
    row = [1, -1, 0, 0]
    col = [(1, 0), (0, 1), (-1, 0), (0, -1)]
    matrix = [[(a * re, a * im) for re, im in col] for a in row]
    total = [(0, 0)] * 5
    for perm in permutations(range(4)):
        term = [(1, 0)] + [(0, 0)] * 4
        for i, j in enumerate(perm):
            for k in range(i + 1, 0, -1):
                term[k] = add(term[k], multiply(term[k-1], matrix[i][j]))
        total = [add(x, y) for x, y in zip(total, term)]
    power_sum = (0, 0)
    for values in matrix:
        for x in values:
            square = multiply(x, x)
            power_sum = add(power_sum, multiply(square, square))
    assert total == [(factorial(4), 0)] + [(0, 0)] * 4
    assert power_sum == (8, 0)
    print("Explicit 4 by 4 polynomial coefficients:", [x[0] for x in total])
    print("Explicit fourth-power sum:", power_sum[0])


if __name__ == "__main__":
    four_by_four()
    print(" n  ordered nonzero multiset pairs  flat pairs")
    for n in range(2, 13):
        tested, flat = flat_count(n)
        print(f"{n:2} {tested:28} {flat:11}")

