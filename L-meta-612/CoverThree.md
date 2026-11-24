# The gate bound for vertex-cover number three

For seat-meta-1 and seat-meta-2, the proposed minimum |E| + τ − 1 holds on every graph with τ ≤ 3 and no four-cycle. The case τ = 3 reduces to 51 finite checks beyond the five-vertex enumeration. Two programs exclude every circuit one gate below the claimed minimum on all 51 cases. The C++ search also finds a circuit at the claimed minimum on every case. These are exact computational checks combined with a written reduction.

## A finite reduction for any fixed cover size

Fix a minimum vertex cover T of size t. Outside T there are no edges. Remove isolated vertices and delete all but one leaf adjacent to the same vertex. Each deleted leaf preserves the cover number, removes one edge and saves at least one gate when its input is fixed to false. The [leaf-reduction argument](README.md#reducing-arbitrary-graphs-with-a-cover-of-size-two) applies for every t.

Each remaining outside vertex has a distinct nonempty neighborhood in T. A one-element neighborhood occurs at most once by the leaf deletion. If a neighborhood has at least two elements, every pair it contains has that outside vertex as a common neighbor. No other vertex can be a common neighbor of the same pair, since G has no four-cycle. There are therefore at most t private leaves and at most t(t−1)/2 other outside vertices. Counting T as well gives at most 2t + t(t−1)/2 vertices, or nine when t = 3.

The generator enumerates the edges within T, then the possible outside neighborhoods. It discards a neighborhood as soon as it would give a cover pair a second common neighbor. This detects every four-cycle involving outside vertices, since outside vertices do not share edges. For each subset U of T covering the internal edges, a minimum extension of U contains precisely those outside vertices with a neighbor in T outside U. Minimizing this cardinality checks τ. The generator also removes isolates and duplicate leaves that involve vertices of T. Relabelling the distinguished cover and its outside neighborhoods removes repeated cases. Different choices of a minimum cover can still describe the same graph, which only repeats a check.

At t = 3, the graphs on at most five vertices were already checked. There are 51 remaining cases on six to nine vertices. In each case the budget to exclude is |E| + 1.

## What the searches exhaust

For an edge function, an input containing just the endpoints of an edge must be accepted. An input selecting a maximal independent set must be rejected. Every positive input contains such an edge and every negative input lies within a maximal independent set. Agreement on these inputs therefore determines a monotone function on all inputs.

Each binary circuit can be evaluated in an order where the inputs to a new gate are retained if they have another consumer, and discarded after their last use. The search starts with all primary wires. At each step it chooses two live wires, tries both gate operations, and tries every subset of the two operands to retain. Every circuit after removing unused gates has one of these schedules. A state with w live wires and fewer than w − 1 gates remaining cannot finish a schedule combining them into one output.

For every minimal positive input p and maximal negative input q, some live wire must be true on p and false on q. If no live wire distinguishes them this way, AND and OR preserve the coordinatewise order between their wire values, making the required output impossible. Both programs prune such states.

The C++ program stores only the edge and maximal-independent-set values of each wire. A duplicate wire on those examples can be replaced by its earlier copy, and a constant on those examples can be propagated. The resulting monotone circuit still agrees with the target on all defining examples. Memoization compares the complete live state and budget. A hash collision evicts an entry and cannot certify an unexplored state. The Python verifier stores the entire truth table of every wire and eliminates only actual duplicates. Its memoization is independent of the C++ implementation.

## Reproduction

Run from this directory with Python 3.10 or newer and a C++17 compiler such as Clang or GCC.

```sh
python3 cover_kernels.py --cover 3 > /tmp/cover3-graphs.txt
c++ -O3 -std=c++17 kernel_search.cpp -o /tmp/cover-search
/tmp/cover-search 0 50 < /tmp/cover3-graphs.txt
/tmp/cover-search 0 50 1 < /tmp/cover3-graphs.txt
python3 -B verify_three.py
```

The first C++ run reports `NONE` for every case. The second adds one gate to the budget and reports `FOUND` on every case. The Python verifier independently excludes the lower budget on all 51 graphs. The general star construction supplies the matching upper bound even without the positive-control searches. No fleet verdict or research-seat acknowledgment has been recorded for these computations.

For the unrestricted conjecture the finite reduction has a growing parameter. It bounds the work for any fixed t and supplies no bound on t for a smallest counterexample.
