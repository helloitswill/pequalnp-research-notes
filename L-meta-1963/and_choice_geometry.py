"""Verify the finite geometry used in the AND-choice bound for L-meta-1963."""

from collections import Counter
from functools import lru_cache
from itertools import combinations


def check_two_group_limit(raw, flags):
    """Pack singleton introductions so that each quadrangle meets at most two groups."""
    groups = [group for size in (1, 2) for group in combinations(range(26), size)]
    group_vertices = [sum(1 << v for v in group) for group in groups]
    rows = [raw[g[0]] | raw[g[-1]] for g in groups]
    flag_hits = [sum(1 << i for i, flag in enumerate(flags) if not flag.isdisjoint(g))
                 for g in groups]
    touches = [sum(1 << i for i, mask in enumerate(rows) if mask & (1 << j))
               for j in range(234)]
    later_disjoint = [sum(1 << j for j in range(i+1, len(groups))
                          if not (verts & group_vertices[j])) for i, verts in enumerate(group_vertices)]

    @lru_cache(None)
    def permitted(saturated_rows):
        forbid = 0
        while saturated_rows:
            bit = saturated_rows & -saturated_rows
            saturated_rows ^= bit
            forbid |= touches[bit.bit_length()-1]
        return ~forbid

    counts = Counter()
    best = 0

    def search(options, once, twice, hit, size):
        nonlocal best
        counts[size] += 1
        best = max(best, hit.bit_count()-size)
        while options:
            bit = options & -options
            options ^= bit
            i = bit.bit_length()-1
            next_twice = twice | (once & rows[i])
            search(options & later_disjoint[i] & permitted(next_twice), once | rows[i],
                   next_twice, hit | flag_hits[i], size+1)

    search((1 << len(groups))-1, 0, 0, 0, 0)
    assert counts == {0: 1, 1: 351, 2: 52975, 3: 112814, 4: 23556, 5: 26}
    assert best == 18
    return best, counts


def main():
    lines = [frozenset((v + d) % 13 for d in (0, 1, 3, 9)) for v in range(13)]
    flags = [frozenset((p, 13+l)) for l, line in enumerate(lines) for p in line]
    heptads = []
    for four in combinations(range(13), 4):
        points = frozenset(four)
        if any(len(points & line) > 2 for line in lines):
            continue
        heptads.append(points | {13+l for l, line in enumerate(lines) if points.isdisjoint(line)})
    assert len(flags) == 52 and len(heptads) == len(set(heptads)) == 234
    # A clause passing every flag and vanishing on H must contain every variable outside H.
    for h in heptads:
        assert len(h) == 7 and all(not flag <= h for flag in flags)
        assert all(any(flag <= h | {v} for flag in flags) for v in range(26) if v not in h)

    raw = [sum(1 << r for r, h in enumerate(heptads) if v in h) for v in range(26)]
    assert min(mask.bit_count() for mask in raw) == 54
    assert max(mask.bit_count() for mask in raw) == 72
    pair_types = Counter()
    eligible = []
    for i, j in combinations(range(26), 2):
        mask = raw[i] | raw[j]
        pair_types[mask.bit_count()] += 1
        if 106 <= mask.bit_count() <= 128:
            eligible.append((i, j, mask))
    triple_min = min((raw[i] | raw[j] | raw[k]).bit_count()
                     for i, j, k in combinations(range(26), 3))
    assert triple_min == 129 and len(eligible) == 130
    assert all((i < 13 and j < 13) or frozenset((i, j)) in flags for i, j, _ in eligible)
    score = max(min((a & ~b).bit_count(), (b & ~a).bit_count())
                for _, _, a in eligible for _, _, b in eligible)
    assert score == 90
    print("Flags, quadrangle supports:", len(flags), len(heptads))
    print("Two-variable ORs by true quadrangle count:", dict(sorted(pair_types.items())))
    print("Minimum true quadrangles for a three-variable OR:", triple_min)
    print("Eligible first AND operands:", len(eligible))
    print("Maximum smaller exclusive count for a pair of eligible operands:", score)
    best, counts = check_two_group_limit(raw, flags)
    print("Families meeting each heptad in at most two groups, by group count:", dict(sorted(counts.items())))
    print("Maximum flags touched minus number of groups:", best)


if __name__ == "__main__":
    main()
