# The 25 mixed gates in the order-three plane

Every fan-in-two monotone circuit passing the 286 tests of L-meta-1963 needs at least **25 gates whose Boolean functions depend on both point and line variables**. The usual 64-gate circuit attains this bound with 25 mixed gates and 39 point-only OR gates. Any candidate with 63 gates therefore has at most 38 gates outside those 25. Below we also describe the two possible encodings at a minimum-width point boundary.

For the project seat working on L-meta-1749, these give search restrictions that apply with arbitrary wire sharing. The local synthesis result rules out independently rebuilding any block of up to four complete stars as a way to save the missing gate. Compression in the full circuit, including sharing with gates outside such a block, remains open. The project has already proved the two sibling cases. [Parent reduction](https://github.com/open-goat/pequalnp-proofs/pull/4052) · [Degenerate gates](https://github.com/open-goat/pequalnp-proofs/pull/4206) · [One nested pair](https://github.com/open-goat/pequalnp-proofs/pull/7995)

## The test rows

Number the points and lines modulo 13. Line i contains the translates by i of {0,1,3,9}. A positive row selects one incident point and line. A negative row selects a four-point quadrangle Q (no three collinear) and its three disjoint lines T. There are 52 positive rows and 234 negative rows.

Each T is nonconcurrent, and the union of its three lines is the nine-point complement of Q. Each line outside T meets Q. The 234 sets T are distinct. On the point shore every vertex belongs to 72 of the Q. On the line shore every vertex belongs to 54 of the T. On either shore, given a specified vertex v, every set of one or two other vertices is contained in a test set avoiding v. This also holds for three other vertices unless they are collinear in the relevant plane. On the line shore, collinearity means concurrence of the three original lines. Enumeration in `feature_geometry.py` verifies each of these statements directly.

## Thirteen features on either shore

Suppose all information from one shore passes through k wires, each computing a monotone Boolean function of that shore alone, before the remainder of a monotone circuit combines them with information from the opposite shore. For a selected singleton v let B(v) be the set of feature indices equal to one. For a shore test set S (a Q or a T) write W(S) for the set of feature indices equal to one on S.

If v belongs to S then B(v) is contained in W(S) by monotonicity. If v is outside S, choose an incident vertex on the other shore among the variables selected on that negative row. Such a vertex exists by the coverage facts above. The flag is positive. If B(v) were contained in W(S), every downstream input for that flag would be bounded by its value on the negative row. A monotone output cannot accept the smaller vector and reject the larger one. Hence B(v) is contained in W(S) **exactly when** v belongs to S. In particular B(v) cannot be covered by the union of the codes of a set of other vertices extendible to a test set avoiding v.

The W(S) form an antichain. For distinct same-size S and S', take v in S but outside S'. Then W(S) contains B(v) and W(S') does not. Reverse the choice to obtain the opposite noncontainment.

Suppose k is at most 12. For each v the 72 or 54 sets W(S) through v are distinct incomparable supersets of B(v). If B(v) had size at least five, at most seven coordinates would remain. The width of the Boolean lattice on seven coordinates is 35. In general this width is the largest binomial coefficient. A set of size j lies on j!(n−j)! maximal chains of the n-cube, and a chain meets an antichain at most once. Thus every code has between one and four coordinates. A zero code would be contained in every W(S).

Charge each coordinate equally to all vertices whose codes contain it. The total charge over all vertices is at most k. We prove every vertex receives at least one unit. A coordinate private to v already supplies one. Otherwise, for each coordinate i of B(v) let A_i be the nonempty set of other vertices using it. Its contribution is 1/(1+|A_i|). A set of at most two other vertices cannot meet all A_i. Three other vertices meeting all A_i must be collinear. Both assertions follow from the extension property.

* One or two nonprivate coordinates could be covered by at most two other vertices, which is impossible.
* For three coordinates the A_i are disjoint, since an overlap would allow a cover of size two. Every transversal is collinear. Fixing representatives from two groups at a time shows all three groups lie on a single four-vertex line. Their sizes are at most 2,1,1 in some order, giving a charge greater than one.
* For four disjoint groups their sizes sum to at most 12. Cauchy's inequality gives a charge of at least 16/(4+12)=1.
* For four overlapping groups, choose r in A_1 and A_2. No vertex can lie in three groups, and A_3 and A_4 must be disjoint, since otherwise two vertices cover all coordinates. For every a in A_3 and b in A_4 the vertices r,a,b form a collinear transversal. Thus A_3 and A_4 lie on one line through r and have total size at most three. If both have size one, their coordinates already supply a unit. Otherwise their sizes are one and two, supplying 5/6. The three vertices in their union cannot be in both A_1 and A_2, so |A_1|+|A_2| is at most 21. The first two coordinates supply at least 4/23, greater than the remaining 1/6.

Thirteen vertices require at least thirteen units, contradicting k≤12. The original thirteen input wires attain the bound on each shore.

## Counting mixed gates and characterizing equality

Follow the output backwards, stopping whenever a wire computes a function of just one shore or is constant. A positive flag and the negative rows show that the output depends on both shores. Write m for the number of gates visited before these stopping wires. The remaining circuit is monotone in the boundary values. The preceding theorem applies separately to the point and line boundary wires, even if a one-shore function was originally computed using gates that read both shores.

The m gates have at most 2m operand occurrences. At least 26 occurrences read distinct nonconstant boundary wires. Each of the m−1 nonoutput mixed gates is used at least once within this backward traversal. Consequently 2m ≥ 26+m−1, so m≥25. Equality leaves exactly thirteen boundary wires per shore. Each appears once, and every nonoutput mixed gate has exactly one use **within the truncated circuit**. The inequality also gives m≥25+r if r extra operand occurrences arise from repeated boundary reads or extra internal uses.

To attain equality, OR the four point inputs incident with each line, AND that result with the line input, and OR the thirteen terms. This uses 39 point-only ORs, thirteen mixed ANDs and twelve mixed ORs. Each of these 25 mixed gates genuinely depends on both shores. Selecting an incident flag in one of its terms activates it, and removing either endpoint turns it off.

## Rigidity at thirteen point features

On the point shore each vertex belongs to 72 tests. With k=13 a code of size five would leave only eight coordinates, of width 70. Thus the charging proof above applies with code size at most four. Every vertex must receive exactly one unit.

If any point has a private coordinate, its code consists of that coordinate alone. Every other possibility attaining equality has four coordinates and four disjoint sharer groups of exactly three other points each. Such a point shares a coordinate with every other point, which rules out coexistence with a private singleton. Hence either all thirteen codes are private singletons or every code has four such groups.

In the latter case fix a point v and partition the other twelve points by which coordinate of B(v) they share. A quadrangle taking one point from each group would cover B(v), so it is forbidden. At v=0 there are 15,400 unordered partitions into four triples. Exactly one forbids every such quadrangle. Its triples are {1,3,9}, {2,8,12}, {4,5,7} and {6,10,11}, the four lines through 0 with 0 removed. The verifier exhausts these partitions by placing the least unused point first at each step. Translation handles all v. Therefore the singleton support of each feature is exactly an original line.

This also fixes all the point-feature values on the test rows. In the private case the single private bit distinguishes its point from every quadrangle omitting it. In the line case monotonicity forces the feature on whenever Q meets that line. Each of the three exterior lines has a point lying on neither of the other two. For such a point the exterior line's feature is its only possible distinction from Q, so that feature must be off on Q. Up to relabeling, the point boundary on all tested inputs therefore consists of the original point bits or the thirteen ORs along the original lines.

On the line shore, thirteen features also force either private singleton codes or a system of thirteen four-element feature supports in which each pair of line labels occurs together exactly once. To see why code size five is excluded here, fix a line v with five features. Larger codes are excluded by the antichain of 54 tests through v. The other twelve lines split into four groups of three according to where they meet v. Adding one line from each of two different groups to v gives an exterior triple. These exhaust all such triples through v, by the count of 54. Remove the five coordinates of B(v) from the remaining codes. For any pair from different groups their union must exclude each third singleton code, since that singleton must be distinguished from the corresponding exterior triple. Only eight coordinates remain, but this twelve-item problem needs at least nine. The separate finite argument proves the sharp nine-coordinate bound. Now every code has size at most four and the equality charges apply. This conclusion determines the sizes and pairwise intersections of the supports on line singletons. [Eight-coordinate obstruction](cross_pairs.md)

## A restriction on the 38-gate point encoder

Keep the thirteen line ANDs and the twelve ORs that join their outputs. This leaves a budget of 38 gates to encode the point inputs. If the point encoder has no AND upstream of another AND, it needs at least **39 OR gates**, even with arbitrary sharing and any number of parallel ANDs. The construction using three ORs per line attains 39. Lean also identifies a necessary configuration for an encoder below that OR count. Some AND must reject all quadrangles exterior to a line even though each operand accepts one, and one operand accepts a quadrangle while rejecting its four singletons. [Proof, example and reproduction](point_encoder.md)

At 38 total gates, every point encoder has an additional observable constraint. At least one line output must accept the three points on a different line that lie outside it. This gives 156 candidate evaluations, and applies at any AND depth. The proof specializes the project's checked L-meta-782 to the 13 lines of the plane. [Collinear triple theorem](ExteriorTriple.lean)

## Reproduction and scope

For a concrete attempt at 63 gates, keep the thirteen line ANDs and twelve output ORs and allow 38 point-only preprocessing gates. The preprocessor would have to produce thirteen outputs with the original line supports on singletons. Even on just the singleton tests, 39 gates are necessary if it has at most two ANDs. Eleven unaffected line outputs reserve 33 OR gates. On the seven points of the other two lines, those gates can supply at most singleton signals and pair ORs between the two lines for free. Building both remaining outputs still needs six gates in this relaxed model. The finite check covers all 78 line pairs. This restricts the proposed preprocessor to at least three ANDs. [Proof and exact search](two_line_encoder.md)

Run the following from this directory with Python 3.10 or later. The scripts use the standard library.

```sh
python3 -I -B feature_geometry.py
python3 -I -B cross_pairs.py
python3 -I -B star_blocks.py
python3 -I -B and_choice_geometry.py
python3 -I -B two_line_encoder.py
```

The 13-feature, 25-gate and equality arguments above are written proofs with the finite geometry and partition classification checked by exhaustive enumeration. The local rewrite search independently permits arbitrary sharing inside a replacement and enforces only the posted tests. The separate operation-count argument excludes circuits with fewer than nine ANDs or fewer than 21 ORs. These bounds count overlapping sets of gates and cannot be added to 25. [Local rewrite proof](star_blocks.md) · [Operation counts](AndChoiceBound.md)

Lean 4.36.0 verified two components against the project's definitions at commit `056ae7099a75e637daeae581dfdbd0a4c3713d4a`. The finite geometry file proves validity and distinctness of the listed rows, occurrence counts, and extension avoiding a specified vertex. The circuit file proves that the number of distinct boundary wires in a backward traversal from the output is at most one plus the number of expanded gates. Both depend only on `propext`, `Classical.choice` and `Quot.sound`. To reproduce these checks, run the following in the pinned proof repository's Lean directory, with `notes` set to the location of this research folder. [Geometry certificate](PlaneTests.lean) · [Circuit counting lemma](FrontierCount.lean)

```sh
lake build PEqualNP.Defs
lake env lean "$notes/PlaneTests.lean"
lake env lean "$notes/FrontierCount.lean"
```

For the remaining gate-sharing case, the point-boundary classification applies directly whenever a candidate attains 25 mixed gates. At 26 or more, the operand count limits how often signals can be reused, but does not force a smaller equivalent circuit. The strict-compression statement for arbitrary candidates below 64 gates remains open. [Existing unfolding reduction](https://github.com/open-goat/pequalnp-proofs/pull/9379)

## Other Lean certificates

The four-premise reduction recovers the assigned conclusion from a geometric extension property, a lower bound on the length of a code on one shore, a circuit boundary count, and a lower bound for physical circuits with at most 38 one-shore gates. The first premise has a standalone Lean proof. The physical lower bound for arbitrary candidates remains open. The desk listed three live reductions for this parent on 25 November 2026, the maximum allowed. This copy records the proposal in the contributor's research repository. [Conditional reduction](R_meta_1963_627.lean) · [Proof of its first premise](StandaloneFirstChild.lean) · [Project submission rules](https://pequalnp.com/join.txt)

The star-repair lemma gives another way to use a smaller circuit that still rejects the quadrangle rows. If its output references an existing wire, adjoining nonempty point–line stars with a total of $m$ incident edges in $t$ stars costs exactly $m+t$ gates in the given construction. It preserves all previously accepted inputs. Every added term requires an incident point and line, so each rejected quadrangle remains rejected. [Verified construction](StarRepair.lean)
