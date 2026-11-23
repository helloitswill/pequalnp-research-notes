"""Exhaustively determine the nine-gate counterexample's two exact minima.

Inputs are six distinct literal wires for the net graph. A possible wire is
represented by its complete 64-input truth table. Search states contain the
wires that may be needed in the future. On each transition any two wires can
compute an AND or OR; each of those input wires may stay live or be discarded
after its final use. Sharing is unrestricted. No graph symmetries are assumed.

Constants, unary gates, repeated operands, and gates outside the output cone
can be removed without increasing either cost or changing surviving wire
functions. Thus the enumeration only needs binary gates on distinct wires.
"""
from functools import lru_cache
from itertools import combinations

N = 6
MASKS = range(1 << N)
EDGES = ((0, 1), (0, 2), (1, 2), (0, 5), (1, 4), (2, 3))
LITERALS = tuple(sum(1 << x for x in MASKS if x & (1 << v)) for v in range(N))
TARGET = sum(1 << x for x in MASKS if any(x & (1 << u) and x & (1 << v) for u,v in EDGES))
SINGLETONS = sum(1 << (1 << v) for v in range(N))
MIN_TRUE = tuple(x for x in MASKS if TARGET >> x & 1 and all(
    not (TARGET >> (x ^ (1 << v))) & 1 for v in range(N) if x & (1 << v)))
MAX_FALSE = tuple(x for x in MASKS if not (TARGET >> x & 1) and all(
    TARGET >> (x | (1 << v)) & 1 for v in range(N) if not x & (1 << v)))


@lru_cache(None)
def distinguished_pairs(wire):
    """A bit for every minimal-positive / maximal-negative pair separated in the desired order."""
    return sum(1 << (i*len(MAX_FALSE)+j)
               for i,p in enumerate(MIN_TRUE) if wire >> p & 1
               for j,n in enumerate(MAX_FALSE) if not (wire >> n & 1))


def reaches(budget, weighted):
    memo = set()
    required_pairs = (1 << (len(MIN_TRUE) * len(MAX_FALSE))) - 1

    def search(wires, left):
        if TARGET in wires:
            return True
        # A binary gate can reduce the live width by at most one. Any valid
        # schedule for a trimmed circuit finishes at just its output.
        if len(wires)-1 > left or left <= 0:
            return False
        key = (tuple(sorted(wires)), left)
        if key in memo:
            return False
        memo.add(key)
        for i,j in combinations(range(len(wires)), 2):
            a,b = wires[i],wires[j]
            others = tuple(w for k,w in enumerate(wires) if k != i and k != j)
            for is_or in (False, True):
                value = (a | b) if is_or else (a & b)
                # This gate could be replaced by an identical live truth table.
                # All generated binary wires are zero at the empty assignment
                # and one at the full assignment, so none can be constant.
                if value in wires:
                    continue
                cost = 1 + int(weighted and is_or and (value & SINGLETONS).bit_count() < 2)
                remaining = left - cost
                if remaining < 0:
                    continue
                for retained in ((), (a,), (b,), (a,b)):
                    next_wires = others + retained + (value,)
                    if len(next_wires)-1 > remaining:
                        continue
                    # If every wire's bit on some positive assignment is <=
                    # its bit on some negative one, any monotone continuation
                    # preserves this order and cannot realize the target.
                    distinguished = 0
                    for wire in next_wires:
                        distinguished |= distinguished_pairs(wire)
                    if distinguished != required_pairs:
                        continue
                    if search(next_wires, remaining):
                        return True
        return False

    result = search(LITERALS, budget)
    print(f"{'Weighted' if weighted else 'Ordinary'} budget {budget}: "
          f"{'FOUND' if result else 'NONE'} ({len(memo)} expanded states).")
    return result


if __name__ == '__main__':
    for budget, weighted, expected in ((7,False,False),(8,False,True),(8,True,False),(9,True,True)):
        if reaches(budget, weighted) != expected:
            raise SystemExit("Unexpected minimum")
