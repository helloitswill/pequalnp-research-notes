"""Two small finite checks for the eight-test K_{3,3,3,3} obstruction."""
from collections import Counter
from itertools import combinations


def antichains(bits):
    def extend(prefix, remaining):
        yield prefix
        for i, new in enumerate(remaining):
            later = [v for v in remaining[i + 1:] if (new & v) != new and (new & v) != v]
            yield from extend(prefix + (new,), later)
    return extend((), list(range(1 << bits)))


def partitions(items):
    """All unordered partitions into blocks of three, sorted by smallest member."""
    if not items:
        yield ()
        return
    for a, b in combinations(items[1:], 2):
        block = (items[0], a, b)
        unused = tuple(v for v in items if v not in block)
        for suffix in partitions(unused):
            yield (block,) + suffix


def color_obstruction(edges, partition):
    group = {v: i for i, block in enumerate(partition) for v in block}
    forced = set()
    incompatible = set()
    for i, j in combinations(range(9), 2):
        if group[i] == group[j]:
            continue
        for k in range(9):
            if k in (i, j) or edges[k] & ~(edges[i] | edges[j]):
                continue
            forced.add(k)
            for v in (i, j):
                incompatible.add(tuple(sorted((k, v))))
    return next((four for four in combinations(sorted(forced), 4)
                 if all(pair in incompatible for pair in combinations(four, 2))), None)


def main():
    width4 = max(map(len, antichains(4)))
    histogram = Counter()
    for antichain in antichains(5):
        if len(antichain) == 9:
            histogram[tuple(sorted({v.bit_count() for v in antichain}))] += 1
    assert width4 == 6
    assert histogram == {(2,): 10, (3,): 10}
    print("Width on four bits:", width4)
    print("Nine-member antichains on five bits: 10 all-pair and 10 all-triple.")
    edges = [sum(1 << i for i in pair) for pair in combinations(range(5), 2)]
    edges.remove(3)  # The missing pair may be fixed by permuting coordinates.
    count = 0
    for partition in partitions(tuple(range(9))):
        clique = color_obstruction(edges, partition)
        assert clique is not None, partition
        count += 1
    assert count == 280
    print("A forced four-clique excludes every one of 280 partitions into triples.")


if __name__ == "__main__":
    main()
