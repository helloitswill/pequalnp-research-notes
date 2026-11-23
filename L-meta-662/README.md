# L-meta-662 · A counterexample on the six-vertex net

The project conjectured a lower bound on the weighted size of circuits detecting edges in graphs with no four-cycle. A six-vertex graph refutes it. The proposed lower bound is **10** and the circuit below has weighted size **9**. This answers the general conjecture assigned in shard 3.

## The graph and circuit

Start with a triangle on vertices 0, 1, and 2. Give each corner a private leaf, joining 0 to 5, 1 to 4, and 2 to 3. This is the net graph. Its only cycle is the triangle. The three disjoint leaf edges require three vertices in any vertex cover, and the triangle vertices themselves cover all six edges. Hence $|E|=6$ and $\tau=3$.

Write $x_i$ for the input bit at vertex $i$. The output is $(P\land Q)\land R$, using these intermediate signals.

| Signal | Computation |
|---|---|
| $P$ | $(x_0\lor x_1)\lor(x_2\land x_3)$ |
| $Q$ | $x_2\lor(x_4\lor x_0)$ |
| $R$ | $(x_5\lor x_1)\lor x_2$ |

If two or more triangle vertices are on, a triangle edge is present and all three signals are true. If all triangle vertices are off, $P$ is false and the selected leaves contain no edge. If exactly one triangle vertex is on, the output reduces to the bit of its private leaf. This accounts for all 64 inputs.

The assignment counts each AND once. It counts an OR once if it fires on at least two different single-vertex inputs, and twice otherwise. Both ORs in $P$ fire on singleton inputs 0 and 1. Both in $Q$ fire on 4 and 0, and both in $R$ fire on 5 and 1. The circuit therefore uses **three ANDs, six wide ORs and zero narrow ORs**. In the project's indexing $A=\{1,7,8\}$, $B=\{0,2,3,4,5,6\}$ and $D=\varnothing$. With $k=3$ the [posted inequality](statement.txt) reads

$$
|E|+2k=6+6=12\quad\le\quad |A|+|B|+2|D|+2=3+6+0+2=11.
$$

## Arbitrarily large shortfalls on connected graphs

Make a chain of $t\ge1$ copies of the net by joining vertex 0 in each copy to vertex 0 in the next. Each new edge is a bridge, so the graph still has no four-cycle. The untouched private-leaf edges form a matching of size $3t$, and the $3t$ triangle vertices cover all $7t-1$ edges.

For each copy with an outgoing bridge, add the next copy's vertex-0 bit as one additional input to its $R$ using a wide OR gate. With only local vertex 0 selected among its triangle vertices, the circuit now accepts either its private leaf or the far end of the outgoing bridge. The other four cases above give the same result as before. Combine the $t$ local outputs with $t-1$ OR gates. Those final ORs are narrow because every local output is false on all singleton inputs. The full circuit has $3t$ ANDs, $7t-1$ wide ORs and $t-1$ narrow ORs. The proposed inequality would require $13t-1\le12t-1$. Each new net increases the deficit by one. Even requiring every vertex to have at least an arbitrarily prescribed number of neighbors leaves unbounded shortfalls. The [connected construction with prescribed minimum degree](ConnectedGraphs.md) proves this stronger statement. These generalizations are written proofs. The Lean file below concerns the six-vertex net.

## Reproduce the finite checks

Run from this directory with Python 3.10 or newer. The programs use only the standard library.

```sh
python3 search_net.py
python3 check_net.py
python3 check_minima.py
python3 check_family.py
```

- [search_net.py](search_net.py) finds three working circuits in the specific three-conjunct family above. Its SHA-256 is `0e6a8257a76d0d80b0010553ce31d3c09e4a31b778331b182c6ea461fce7d3c2`, the fingerprint sent with the desk return.
- [check_net.py](check_net.py) checks every input, the graph hypothesis, all possible vertex covers, and each gate's singleton outputs. It reproduces $12>11$.
- [check_minima.py](check_minima.py) independently searches arbitrary fan-in-two monotone circuits with sharing. It finds that the exact ordinary minimum is **8** and the exact weighted minimum is **9**. The ordinary budget of 7 and the weighted budget of 8 both fail. These minima are computational results. A single nine-gate witness already suffices to refute L-meta-662.

The [family checker](check_family.py) tests all 64 local truth patterns and the graph properties of six finite members of the connected construction.

The exhaustive program tracks each live wire's complete 64-bit truth table. A new gate can keep either, both, or neither operand for future use. Every nonredundant circuit has such a last-use schedule. The circuit can discard a duplicate signal and propagate constants without changing the surviving truth tables or their weights. A state with $w$ live wires needs at least $w-1$ further gates to combine them. The program also prunes a state if its wires can no longer distinguish some minimal true assignment from a maximal false assignment in the monotone direction.

The separate L-meta-612 conjecture concerns ordinary size and would give $|E|+\tau-1=8$ on this graph. The ordinary minimum attains that prediction here.

## Reproduce the Lean refutation

[L_meta_662.lean](L_meta_662.lean) proves the negation of the [exact assigned statement](statement.txt). An independent Lean type check against that statement reported only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

Use a clean checkout of [the upstream project at 096c200](https://github.com/brilliant-hq/pequalnp-proofs/tree/096c2001d7005ecbf8c5635a7d5a9df31bbddd0b) with its pinned Lean 4.36.0 toolchain. From the root of that checkout, set `notes` to this note's directory and run

```sh
notes=/absolute/path/to/pequalnp-research-notes/L-meta-662
(cd lean && lake exe cache get)
mkdir -p lean/PEqualNP/Outside
cp "$notes/L_meta_662.lean" lean/PEqualNP/Outside/L_meta_662.lean
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_662.lean "$notes/statement.txt" refute
```

The proof file's SHA-256 is `06cc47c21b6eff72be104f12ceac933227d2e26ac4dbea84178d0b03ab02716a`. The exact statement's SHA-256 is `287b85a7c5d2ce074956602570e745fc1665240e7430f7e3129d393562942a08`.
