# Searching for a 103-OR circuit on 42 inputs

L-meta-2378 asks for the full point–line incidence edge function of the projective plane of order four using at most 103 binary OR gates. Binary AND gates are unlimited. The exact result remains open in this investigation. A 125-gate construction uses 104 ORs and 21 ANDs. Lean verified its output on all Boolean assignments by symbolically expanding the circuit to precisely the 105 prescribed incidence pairs. It also computed the OR count in the assignment’s own set-cardinality expression. [Checked baseline and reusable correctness lemma](StarBaseline.lean)

## A saving must involve at least ten inputs in a local construction

A local circuit using `k` OR gates can be completed to a full witness if it accepts at least `k+2` of the incidence-pair inputs and rejects every independent set. Append an AND for each incidence it misses and OR those terms into its output. We ruled out this approach on every choice of at most nine inputs, including candidates allowed to return true on larger sets whenever they contain some genuine incidence.

The proof removes vertices of degree zero or one in the graph of accepted pairs. Bipartiteness and the absence of four-cycles leave four possible cores. Their exact OR minima are 5 for the six-cycle, 7 for the eight-cycle, 8 for three internally disjoint paths of lengths 3, 3, 3 joining two vertices, and 9 for paths of lengths 2, 4, 4. Searches allowed arbitrarily many AND gates. The four exclusions have separately replayed LRAT certificates. The classifier and reductions to the encoded searches are mathematical arguments. A separate written proof treats chordless cycles of any length at least five. Four denser ten-input searches reached their time limits. [Proof and reproduction](LocalGadgets.md) · [Encoder and certificate checker](local_or_search.py)

## Tests on the full plane

The 105 edge inputs and 25,237 maximal independent sets suffice to certify a candidate monotone circuit. For every union of line neighborhoods, the generator selects all points outside the union and all lines contained in the union. These are exactly the maximal independent inputs. A separate enumeration over all 2,097,152 point subsets confirmed the same collection. Every positive input contains an edge, and every negative input is contained in one of the maximal independent inputs. [General boundary-test theorem](../L-meta-2029/BoundaryTests.lean)

We tested rewrites of the direct edge formula and point-centered, line-centered and mixed star formulas. The program cuts connected groups of one, two or three original OR gates, skipping intervening AND gates. It tries to use one fewer OR with unrestricted conjunctions of all unaffected input and gate wires. The original circuit above the cut is evaluated on the exact boundary to determine which rows the replacement must satisfy.

For a fixed set of positive rows, the strongest available conjunction joins every unaffected signal true on all those rows. One OR permits a disjunction of two such conjunctions. With two ORs and free ANDs, distributing the common conjunctions gives either a disjunction of at most three conjunctions, or an AND of two two-term disjunctions. The search enumerates the possible positive supports and checks the negative inputs in parallel using integer bitsets. Across 1,024 formulas generated with 256 seeds, no replacement saved an OR in the 106,496 one-OR windows, 105,472 two-OR windows, or 148,098 three-OR windows tested. A four-cycle control found and verified the expected one-OR saving. [Window search](window_search.py)

A second search considered sharing one new OR of two conjunctions of raw inputs. Any arm useful on a two-variable positive input can be taken as a single vertex or an incidence pair. Across 128 formulas, 10,521 nonredundant arm pairs yielded 18,302 individual substitutions. No helper enabled substitutions at two different gates in the same formula. These finite searches leave other ways of sharing and recomputing gates open. [Shared helper search](shared_helper.py)

## Additional restrictions

An eight-vertex maximal independent set leaves the OR of 34 remaining inputs, giving an unconditional lower bound of 33 OR gates. Lean checked the lower bound for the project’s exact circuit semantics and OR count. Another restriction rules out circuits that expose all 21 line-neighborhood disjunctions when all points are fixed to false. Those circuits need at least 104 ORs, even when gates mix the two shores on other assignments. [Argument, sources and proof scope](OppositeFaces.md) · [Cofactor verification](MaximalCorner.lean) · [Gate-count disjointness](OppositeFaces.lean)

## Reproduction

The Lean files use the project’s pinned Lean 4.36.0 environment. From its `lean` directory, set `NOTES` to the absolute path of this folder. [Pinned project source](https://github.com/open-goat/pequalnp-proofs/tree/056ae7099a75e637daeae581dfdbd0a4c3713d4a)

```sh
lake env lean "$NOTES/StarBaseline.lean"
lake env lean "$NOTES/OppositeFaces.lean"
lake env lean "$NOTES/MaximalCorner.lean"
python3 "$NOTES/window_search.py" --seeds 256
python3 "$NOTES/shared_helper.py" --seeds 32
```

The local synthesis checks use CaDiCaL 2.1.2. The four commands in the local-gadget note regenerate their proof traces. Run Python with assertions enabled. Independent research by helloitswill with AI assistance.
