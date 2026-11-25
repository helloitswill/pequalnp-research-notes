# Gate counts from the 234 quadrangle tests

Any binary AND/OR circuit passing the 52 positive flags and 234 negative quadrangle tests of L-meta-1963 has **at least nine AND gates**. It also has **at least twenty-one OR gates**. These separate lower bounds hold for arbitrary fan-out and do not require the nested-AND hypothesis.

## Each rejected quadrangle forces its own clause

Let H be the seven selected variables on a quadrangle input, four points and their three avoiding lines. H contains no flag. Adding any variable outside H creates a flag. The program checks these facts directly for every H in the posted labeling.

An OR of raw inputs that accepts every flag and rejects H must have support exactly the 19-variable complement of H. Its support misses H. If it also missed a variable v outside H, the flag in H together with v would be rejected. Consequently, one such clause can reject at most one quadrangle. A pure monotone CNF fitting the tests therefore needs at least 234 different clauses, and the conjunction of the 234 complement clauses attains that clause count.

## Counting choices at the AND gates

Write A for the number of binary AND gates. Choose one of the two operands independently at every AND and replace the gate by a copy of that operand. All other gates are ORs. The resulting output is a single OR of raw variables. It accepts all flags because these replacements can only increase wire values.

On a fixed quadrangle H, let m(H) count the AND gates whose two operands have opposite truth values in the original circuit. At each of these gates choose the false operand. Either choice is allowed at each other AND. By induction on gate order, every resulting wire has its original value on H. Thus H gets at least 2^(A−m(H)) choices of a clause rejecting it. Different quadrangles get disjoint sets of choices. Dividing by 2^A gives the bound

$$
\sum_H 2^{-m(H)} \le 1.
$$

In particular A≥8 since there are 234 quadrangles. Suppose A=8. Focus on the first AND in evaluation order and call its two input functions f and g. Each is an OR of raw variables. Write e_f for the number of quadrangles with f true and g false, and e_g for the number with g true and f false.

Fix the choice of f at this first gate. There are only 128 settings of the remaining seven gates. Every quadrangle except the e_f rows is still covered by the counting argument, so 234−e_f≤128. Reversing the choice gives e_g≥106 as well. Each operand therefore hits between 106 and 128 quadrangles, since it must miss at least the 106 exclusive hits of the other operand.

A single variable hits 54 or 72 quadrangles. Every union of three distinct variables hits at least 129. Of the 325 distinct two-variable ORs, 130 hit between 106 and 128. They are exactly the 78 point pairs and the 52 incident point-line pairs, and each hits 126 quadrangles. Among ordered pairs of these 130 operands, the largest possible value of min(e_f,e_g) is 90. This contradicts 106 and proves A≥9.

## Counting OR gates

Let O be the total number of OR gates. For each heptad H pick one of its AND choices from the proof above. Its clause has 19 essential variables. The output cone of a binary OR circuit with r gates contains at most r+1 distinct input variables, by counting graph edges in the connected cone. Thus at least 18 distinct OR gates reach the clause output. They are all false on H, since false at an OR implies false at both its inputs. The chosen replacements reproduce every original wire on H. In particular, **at most O−18 original OR gates can be true on H**.

Suppose each heptad makes at most two OR gates true. Assign every raw variable whose singleton input makes an OR gate true to the earliest such OR in evaluation order. Ignore ORs assigned no variables, and call the nonempty groups B₁,…,Bₜ. When a previously unassigned variable v first makes an OR true, at least one operand is already true on the singleton v. Every ancestor of that operand which is true on the singleton must be an AND or the raw input v. At each such AND both inputs are true there. Recursing shows that this operand computes exactly the projection v. In particular a group contains at most two variables. Groups are disjoint, and by monotonicity each heptad intersects at most two groups.

The finite geometry calculation chooses every increasing family of disjoint one- or two-variable groups satisfying this constraint. A new group is permitted exactly when it misses all heptads already touching two groups. Let hit denote the number of distinct flags incident with the union of the groups. The maximum of hit−t is 18. The numbers of families at group counts 0 through 5 are 1, 351, 52,975, 112,814, 23,556 and 26. Larger families do not occur.

Set every grouped raw variable to zero. The restricted circuit still accepts all 52−hit outside flags. It rejects each singleton because the original circuit rejects every heptad and each singleton is contained in a heptad. Each of the t assigned ORs now has an identically zero projection operand and can be bypassed. Every remaining OR is false on all singleton inputs by construction. On the remaining variables any wire true on a singleton must be a projection. Tracing through each AND follows two operands that are both true on that singleton. This trace never encounters an OR. Fixed inputs may also be zero.

In this restricted circuit, every singleton-rejecting output can accept at most r+1 different flags if it uses at most r OR gates. To see this, bypass every AND having a singleton-rejecting operand toward such an operand. This can only increase the output, and all originally singleton-rejecting wires remain singleton-rejecting by induction on the circuit. An AND with two projection operands is either a projection or a two-variable conjunction. The latter accepts at most one flag if its variables are distinct. The resulting singleton-rejecting output therefore is an OR of at most r+1 such terms or constant zeros. The count applies to DAGs because the connected output cone of r binary OR nodes can join at most r+1 leaves.

Taking r=O−t gives 52−hit ≤ O−t+1, hence **O≥33 whenever every heptad makes at most two ORs true**. In particular O≤20 would force at most two true ORs per heptad by the 19-variable clause argument, contradicting this bound. Therefore O≥21.

The two-group condition matters. Pairing the thirteen line variables into six disjoint pairs and one singleton touches all 52 flags. Each heptad meets at most three of these groups, since it contains exactly three lines. This prevents extending the same two-group counting bound to three.

## Reproduction and scope

Run `python3 -B and_choice_geometry.py` in this directory. The script directly builds and verifies the supports and exhausts the raw singletons, pairs, triples, 130² pairs of eligible AND operands, and all possible families of fresh singleton groups meeting each heptad at most twice. An independent calculation forbade each triple of raw vertices that occurs in a heptad from lying in three distinct groups. It reproduced all six family counts and the maximum of 18. The circuit argument above is mathematical. These operation counts exclude candidate shapes from a search. The proof of strict compression in the full assignment remains open.
