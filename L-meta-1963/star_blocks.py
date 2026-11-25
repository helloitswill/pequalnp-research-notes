"""Cost of replacing a block of complete point stars or line stars in PG(2,3)."""
from collections import Counter
from functools import cache
from itertools import combinations


LINES = [frozenset((w + d) % 13 for d in (0, 1, 3, 9)) for w in range(13)]
QUADRANGLES = [set(points) for points in combinations(range(13), 4)
               if all(len(line.intersection(points)) <= 2 for line in LINES)]
NEGATIVES = [q | {13 + w for w, line in enumerate(LINES) if line.isdisjoint(q)}
             for q in QUADRANGLES]


def shrink_block(centers, line_centers):
    """Keep all shared leaves; remove private leaves by fixing them to zero."""
    if line_centers:
        neighbors = [LINES[c] for c in centers]
    else:
        neighbors = [{w for w, line in enumerate(LINES) if c in line} for c in centers]
    universe = set().union(*neighbors)

    def membership(leaf):
        return sum(1 << i for i, ns in enumerate(neighbors) if leaf in ns)

    shared = sorted((v for v in universe if membership(v).bit_count() >= 2),
                    key=membership)
    private = [sorted(ns.difference(shared)) for ns in neighbors]
    # With just one common leaf, retain one private leaf on all but one of
    # three centers. For two centers retain both private leaves.
    retained = max(2, len(centers) - 1) if len(shared) == 1 else 0
    leaves = shared + [ns[0] for ns in private[:retained]]
    removed = sum(map(len, private)) - retained

    other_offset = 0 if line_centers else 13
    center_offset = 13 - other_offset
    vertices = [c + center_offset for c in centers] + [v + other_offset for v in leaves]
    p = tuple(sorted((1 << i) | (1 << (len(centers) + j))
                     for i, ns in enumerate(neighbors) for j, v in enumerate(leaves) if v in ns))
    projected = {sum(1 << i for i, v in enumerate(vertices) if v in row) for row in NEGATIVES}
    q = tuple(sorted(mask for mask in projected
                     if not any(mask != r and mask & r == mask for r in projected)))
    budget = 5 * len(centers) - 2 - removed
    return len(vertices), p, q, budget, removed


def search(n, positives, negatives, budget, restriction_costs=()):
    """Exhaust topological schedules, retaining each operand until its last use."""
    rows = positives + negatives
    target = (1 << len(positives)) - 1
    boundary_size = len(rows)
    full_boundary = (1 << boundary_size) - 1
    if restriction_costs:
        # A non-star graph has a surviving edge after each single deletion.
        # The circuit must be true on each of these extra rows.
        assert all(any(not (e >> v & 1) for e in positives) for v in range(n))
        rows += tuple(((1 << n) - 1) ^ (1 << v) for v in range(n))
        target |= ((1 << n) - 1) << boundary_size
    full = (1 << len(rows)) - 1
    primary = tuple(sorted(sum(((mask >> v) & 1) << i for i, mask in enumerate(rows))
                           for v in range(n)))
    required = (1 << (len(positives) * len(negatives))) - 1

    @cache
    def separates(wire):
        rejected = (full_boundary & ~wire) >> len(positives)
        return sum(rejected << (i * len(negatives)) for i in range(len(positives))
                   if wire >> i & 1)

    # For each vertex, slack is the remaining allowance of removable gates
    # minus the number of live wires which vanish when that input is false.
    initial_slack = tuple(budget - lower - 1 for lower in restriction_costs)

    @cache
    def spend(slack, mask):
        return tuple(value - ((mask >> i) & 1) for i, value in enumerate(slack))

    @cache
    def visit(wires, left, slack):
        if target in wires:
            return True
        if left == 0 or len(wires) - 1 > left:
            return False
        for a, b in combinations(wires, 2):
            others = tuple(v for v in wires if v != a and v != b)
            base = 0
            for v in others:
                base |= separates(v)
            vanishes_a = (full ^ a) >> boundary_size
            vanishes_b = (full ^ b) >> boundary_size
            for v, extra_cost in ((a & b, vanishes_a ^ vanishes_b), (a | b, 0)):
                if v in wires or v == 0 or v == full:
                    continue
                for keep in ((), (a,), (b,), (a, b)):
                    if len(others) + len(keep) + 1 > left:
                        continue
                    after = spend(slack, extra_cost)
                    for retained in keep:
                        after = spend(after, (full ^ retained) >> boundary_size)
                    if any(value < 0 for value in after):
                        continue
                    sep = base | separates(v)
                    for retained in keep:
                        sep |= separates(retained)
                    if sep == required and visit(tuple(sorted((*others, *keep, v))), left - 1, after):
                        return True
        return False

    result = visit(primary, budget, initial_slack)
    states = visit.cache_info().currsize
    visit.cache_clear()
    separates.cache_clear()
    spend.cache_clear()
    return result, states


def restriction(n, positives, negatives, vertex):
    kept = [e for e in positives if not (e & (1 << vertex))]
    active = [v for v in range(n) if any(e & (1 << v) for e in kept)]

    def project(mask):
        return sum(((mask >> v) & 1) << i for i, v in enumerate(active))

    p = tuple(sorted(map(project, kept)))
    raw = set(map(project, negatives))
    q = tuple(sorted(a for a in raw if not any(a != b and a & b == a for b in raw)))
    return len(active), p, q


@cache
def exact_cost(n, p, q):
    if not p:
        return 0  # Only used as a lower bound for an edgeless restriction.
    # An edge and its two singleton restrictions witness essentiality of its
    # endpoints. All remaining vertices have an edge and a tested singleton.
    assert all(any(mask & (1 << v) for mask in q) for v in range(n))
    assert all(not any(e & mask == e for e in p) for mask in q)
    cover = min(mask.bit_count() for mask in range(1 << n) if all(mask & e for e in p))
    upper = len(p) + cover - 1
    if upper == n - 1:
        return upper
    sub = tuple(exact_cost(*restriction(n, p, q, v)) for v in range(n))
    lower = max(n - 1, max(sub) + 1)
    assert lower <= upper
    for budget in range(upper - 1, lower - 1, -1):
        found, _ = search(n, p, q, budget, sub)
        if not found:
            return budget + 1
    return lower


def main():
    print(f"{len(QUADRANGLES)} quadrangle negatives")
    for k in (2, 3, 4):
        types = Counter(shrink_block(centers, dual) for dual in (False, True)
                        for centers in combinations(range(13), k))
        summary = Counter()
        for (n, p, q, budget, deleted), copies in types.items():
            cost = exact_cost(n, p, q)
            if cost != budget + 1:
                raise ValueError((n, p, q, budget, cost))
            summary[(deleted, cost)] += copies
        for (deleted, cost), copies in sorted(summary.items(), reverse=True):
            print(f"{copies} blocks of {k} stars: {deleted} private leaves removed, "
                  f"reduced minimum {cost}, full block minimum {cost + deleted}.")


if __name__ == "__main__":
    main()
