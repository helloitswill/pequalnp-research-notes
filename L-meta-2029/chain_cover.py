"""Certify the minimum number of chain-graph factors for two biaffine edge functions.

Point (x,y) and line y=a*x+b are numbered q*x+y and q*a+b on their respective shores.
A mask denotes a vertex set on one shore. An order makes every column neighborhood
a prefix by extending it to the last of its incident points in that order.
Run with --certificate FILE to export all witnesses and point orders as JSON.
"""

import argparse
import json
from itertools import combinations
from pathlib import Path


def points_in(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def columns_for_graph(q):
    return [
        sum(1 << (x*q + (a*x+b) % q) for x in range(q))
        for a in range(q) for b in range(q)
    ]


def all_unions(columns):
    unions = [0]
    for col in columns:
        unions += [old | col for old in unions]
    return unions


def certify_width(unions):
    # Maximum matching in two copies of the strict inclusion order pairs consecutive
    # members of chains. Left-to-right unmatched edges and right-to-left matched
    # edges give an antichain of the same cardinality as the resulting chain cover.
    size = len(unions)
    successors = [
        [j for j, b in enumerate(unions) if a != b and a & b == a]
        for a in unions
    ]
    successor = [-1] * size
    predecessor = [-1] * size

    def augment(i, seen_right):
        for j in successors[i]:
            if j in seen_right:
                continue
            seen_right.add(j)
            previous = predecessor[j]
            if previous == -1 or augment(previous, seen_right):
                successor[i] = j
                predecessor[j] = i
                return True
        return False

    for i in range(size):
        augment(i, set())

    reached_left = {i for i, j in enumerate(successor) if j == -1}
    reached_right = set()
    pending = list(reached_left)
    while pending:
        i = pending.pop()
        for j in successors[i]:
            if j == successor[i] or j in reached_right:
                continue
            reached_right.add(j)
            partner = predecessor[j]
            if partner == -1:
                raise AssertionError('An augmenting path remains')
            if partner not in reached_left:
                reached_left.add(partner)
                pending.append(partner)

    antichain = [unions[i] for i in sorted(reached_left - reached_right)]
    chains = []
    for i in range(size):
        if predecessor[i] != -1:
            continue
        chain = []
        while i != -1:
            chain.append(unions[i])
            i = successor[i]
        chains.append(chain)

    # These checks give independently inspectable lower and upper certificates.
    assert len(antichain) == len(chains)
    assert all(u & v not in (u, v) for u, v in combinations(antichain, 2))
    assert sorted(u for chain in chains for u in chain) == sorted(unions)
    assert all(u != v and u & v == u for chain in chains for u, v in zip(chain, chain[1:]))
    return chains, antichain


def extend_chain(chain, shore_size):
    order = []
    previous = 0
    full = (1 << shore_size) - 1
    for mask in [*chain, full]:
        order.extend(points_in(mask & ~previous))
        previous = mask
    assert sorted(order) == list(range(shore_size))
    return order


def prefix_completion(order, columns):
    prefixes = [0]
    for point in order:
        prefixes.append(prefixes[-1] | 1 << point)
    return [next(prefix for prefix in prefixes if col & prefix == col) for col in columns]


def certificate(q):
    n = q*q
    columns = columns_for_graph(q)
    target_unions = all_unions(columns)
    family = sorted(set(target_unions), key=lambda mask: (mask.bit_count(), mask))
    chains, antichain = certify_width(family)
    orders = [extend_chain(chain, n) for chain in chains]
    factors = [prefix_completion(order, columns) for order in orders]
    for factor in factors:
        assert all(a & b == a for a, b in zip(columns, factor))
        assert all(a & b in (a, b) for a, b in combinations(factor, 2))

    # Each Python bit indexes one LEFT subset. The outer iteration fixes one RIGHT
    # subset. Intersect the positive truth tables of all actual completed graphs.
    total_subsets = 1 << n
    all_left_rows = (1 << total_subsets) - 1
    accepts = [
        sum(1 << left for left in range(total_subsets) if left & neighborhood)
        for neighborhood in range(total_subsets)
    ]
    factor_unions = [all_unions(factor) for factor in factors]
    inputs_checked = 0
    for right, target in enumerate(target_unions):
        prediction = all_left_rows
        for unions in factor_unions:
            prediction &= accepts[unions[right]]
        assert prediction == accepts[target], f'Full-function mismatch at right mask {right}'
        inputs_checked += total_subsets

    assert (len(chains), inputs_checked) == {2: (4, 256), 3: (36, 262144)}[q]
    # The following witnesses also specify actual line subsets realizing every
    # incomparable union. Distinct unions in the antichain require distinct orders.
    right_witness = {}
    for right, union in enumerate(target_unions):
        right_witness.setdefault(union, right)
    return {
        'q': q,
        'neighborhood_unions': len(family),
        'minimum_factor_count': len(orders),
        'full_inputs_checked': inputs_checked,
        'antichain': [
            {'left_union_mask': mask, 'right_subset_mask': right_witness[mask]}
            for mask in antichain
        ],
        'chains_of_left_union_masks': chains,
        'point_orders': orders,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--q', type=int, choices=(2, 3))
    parser.add_argument('--certificate', type=Path, help='export the complete certificates as JSON')
    args = parser.parse_args()
    results = [certificate(q) for q in ([args.q] if args.q else [2, 3])]
    if args.certificate:
        args.certificate.write_text(json.dumps(results, indent=2) + '\n')
    for result in results:
        print('q={q}  unions={neighborhood_unions}  minimum chain factors={minimum_factor_count}  '
              'full inputs checked={full_inputs_checked}'.format(**result))
