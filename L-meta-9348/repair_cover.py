"""Check which sets of rectangles in nearCover can be kept in a full cover."""
import ast
import itertools
import json
from pathlib import Path
import re
import sys


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


source = Path(__file__).with_name("PuncturedPlaneCover.lean").read_text()
def read_list(name):
    match = re.search(r"def " + name + r"\s*:.*?:=\s*(\[[^\]]+\])", source, re.S)
    return ast.literal_eval(match.group(1))


rows = read_list("rows")
near = read_list("nearCover")
n = len(rows)
full = (1 << n) - 1
zeros = sum((row ^ full) << (n*i) for i, row in enumerate(rows))
def cells(a, b):
    return sum(b << (n*i) for i in indices(a))


grids = [cells(a, b) for a, b in near]
conflicts = []
for i in range(n):
    for j in range(n):
        conflicts.append(zeros & sum(
            (full if row >> j & 1 else rows[i]) << (n*r) for r, row in enumerate(rows)))


def clique(candidates, size):
    if size == 1:
        return [next(indices(candidates))] if candidates else None
    while candidates.bit_count() >= size:
        v = (candidates & -candidates).bit_length() - 1
        candidates ^= 1 << v
        found = clique(candidates & conflicts[v], size - 1)
        if found is not None:
            return [v, *found]
    return None


def coloring(candidates, size):
    groups = [0] * size

    def visit(remaining, used):
        if not remaining:
            return True
        choice = None
        for v in indices(remaining):
            bad = conflicts[v]
            allowed = [i for i in range(used) if not groups[i] & bad]
            if used < size:
                allowed.append(used)
            if not allowed:
                return False
            key = (len(allowed), -(bad & remaining).bit_count())
            if choice is None or key < choice[0]:
                choice = key, v, allowed
        _, v, allowed = choice
        for i in allowed:
            groups[i] |= 1 << v
            if visit(remaining ^ (1 << v), max(used, i + 1)):
                return True
            groups[i] ^= 1 << v
        return False

    if not visit(candidates, 0):
        return None
    result = []
    for group in groups:
        if group:
            a = b = 0
            for v in indices(group):
                i, j = divmod(v, n)
                a |= 1 << i
                b |= 1 << j
            assert not cells(a, b) & ~zeros
            result.append((a, b))
    return result


if __name__ == "__main__":
    size = int(sys.argv[1])
    assert 1 <= size <= len(near)
    witnesses = []
    by_coloring = 0
    for removed in itertools.combinations(range(len(near)), size):
        keep = [i for i in range(len(near)) if i not in removed]
        missing = zeros
        for i in keep:
            missing &= ~grids[i]
        block = clique(missing, size + 1)
        if block:
            assert all(conflicts[v] >> w & 1 for v, w in itertools.combinations(block, 2))
            witnesses.append([list(removed), block])
            continue
        solved = coloring(missing, size)
        if solved is not None:
            result = [near[i] for i in keep] + solved
            painted = 0
            for ab in result:
                painted |= cells(*ab)
            assert len(result) <= 14 and painted == zeros
            path = Path(__file__).with_name("full-cover.json")
            path.write_text(json.dumps(result) + "\n")
            print("Full cover:", path)
            sys.exit()
        by_coloring += 1
    print("Rectangles replaced:", size, "| clique certificates:", len(witnesses),
          "| excluded by exhaustive coloring:", by_coloring)
