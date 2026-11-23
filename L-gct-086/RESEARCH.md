# What can be bounded on a constant-permanent space?

Research notes for **L-gct-086** · 23 November 2026

Write \(J\) for the \(n\times n\) matrix of ones. A complex linear space \(L\) is a *level space* here if \(\operatorname{per}(J+T)=n!\) for every \(T\in L\). The assignment asks for an absolute \(C\) such that every such space has dimension at most \(Cn\). **That assertion remains unresolved in this work.**

## Results at a glance

| Hypothesis | Conclusion | Verification |
| --- | --- | --- |
| Rows vary independently in a level space | Dimension at most \(n-1\), attained for \(n\ge1\) | Written proof using Lovitz–Petrov. The row-matching coefficient step has a Lean proof |
| Every row and column of every direction sums to zero, \(n\ge3\) | Dimension at most \(\lfloor(n^2-1)/3\rfloor\) | Written proof. Lean checks the cubic matching identity |
| Basis matrices each have at most two nonzero entries, $n\ge2$ | Sharp bound $2n-3$ | Written proof in section 7 |
| A proposed proof requires the \(k\)th entrywise power sum to vanish throughout every centered level space | A counterexample exists for each \(k\ge4\) | Written family. Lean checks the general rotation criterion and all claims about the \(4\times4\) example |
| A permutation group certifies a space by the absence of invariant polynomials in degrees \(1,\ldots,n\) | Dimension at most \(n-1\) | Written proof. An independent finite abelian group counting bound also has a Lean proof |

These bounds make no assumption that an arbitrary level space splits into row-supported and column-supported directions. Their overlap with the project's internal lemmas has not been established.

## 1. A tensor dimension bound

Let \(s\ge1\), let \(U_i\subseteq\mathbb C^s\) be vector spaces, and suppose that for \(m\) independently chosen \(u_i\in U_i\),
\[
  \sum_{j=1}^s\prod_{i=1}^m(1+u_i(j))=s.
\]
Then \(\sum_i\dim U_i\le s-1\).

For \(m\ge2\), put \(V_i=\mathbb C\oplus U_i^*\), \(a_{ij}=(1,\mathrm{ev}_j|_{U_i})\) and \(a_{i0}=(1,0)\). Form \(z_j=\bigotimes_i a_{ij}\). Evaluating on the tuples \((1,u_i)\) gives \(\sum_{j=1}^s z_j=s z_0\). The test functionals \((1,u_i)\) span \(V_i^*\) in each factor, so this is a tensor identity.

The multiset \(z_0,\ldots,z_s\) is connected in the sense of the product-tensor splitting theorem. In a nontrivial direct-sum partition of its span, the component containing no \(z_0\) would have to sum to zero. Testing at \(u_i=0\) sends each of its terms to 1. Its sum would be a positive integer. Coordinate evaluations span \(U_i^*\), so the factor spans have dimensions \(1+\dim U_i\). The splitting theorem therefore gives
\[
  1+\sum_i\dim U_i\ \le\ \dim\operatorname{span}(z_0,\ldots,z_s)\ \le\ s.
\]
For \(m=1\) the premise places \(U_1\) in the kernel of the nonzero coordinate-sum functional, proving the same result. [Lovitz and Petrov, *A generalization of Kruskal's theorem on tensor decomposition*, Theorem 4](https://doi.org/10.1017/fms.2023.20)

## 2. Independently variable rows

Write \(L=\bigoplus_i e_i\otimes U_i\), so each row can be selected from its own \(U_i\subseteq\mathbb C^n\). Fix any rows \(u_i\in U_i\). Multiplying the chosen rows by independent scalars and taking the coefficient on a nonempty set \(S\) of rows gives
\[
  (n-|S|)!\sum_{f:S\hookrightarrow[n]}\prod_{i\in S}u_i(f(i))=0.
\]
The factorial counts completions of that partial permutation. The exact coefficient can also be recovered by independently keeping or deleting rows. This latter formulation is verified in **RowCoefficients.lean**.

Define \(p_S=\sum_j\prod_{i\in S}u_i(j)\). For any map \(f:S\to[n]\) its injectivity indicator is the sum of the signs of all permutations of \(S\) that preserve \(f\). If a fiber has two or more points, composing with a transposition in that fiber cancels the terms in pairs. Otherwise only the identity occurs. The injection sum above consequently equals
\[
  \sum_{\tau\in\operatorname{Sym}(S)}\operatorname{sgn}(\tau)
       \prod_{B\text{ a cycle of }\tau}p_B .
\]
Induct on \(|S|\). Every permutation with more than one cycle has a proper nonempty cycle whose factor vanishes. The remaining \((|S|-1)!\) full cycles have the same sign, so \(p_S=0\). Expanding the row product now gives \(\sum_j\prod_i(1+u_i(j))=n\). Section 1 yields \(\dim L\le n-1\). A single row with coordinate sum zero realizes equality. For \(n=0\) the ambient vector space is zero.

For an arbitrary level space, all of its row-supported directions together span a space of dimension at most \(n-1\), since their sum is an independently variable row space inside \(L\). Transposition gives the analogous statement for column-supported directions. This leaves open how many further directions couple several rows and columns.

## 3. What survives for all centered spaces

Suppose \(T\) has zero row and column sums. For \(r\le n\), the coefficient of \(z^r\) in \(\operatorname{per}(J+zT)\) is \((n-r)!/r!\) times the sum of ordered products of \(r\) entries in distinct rows and distinct columns. A set of \(r\) entries in a matching has \(r!\) orderings and \((n-r)!\) permutation completions.

For \(r=2\) the ordered sum is \(\sum_{ij}T_{ij}^2\). For \(r=3\) it is \(4\sum_{ij}T_{ij}^3\). To see the factors, for zero-sum vectors \(f,g,h\) on a finite set, direct exclusion of coinciding indices gives
\[
 \sum_{a\ne b}f_a g_b=-\sum_a f_a g_a,\qquad
 \sum_{a,b,c\ \mathrm{distinct}}f_a g_b h_c=2\sum_a f_a g_a h_a .
\]
Apply the relevant formula to column indices and then to row indices. **CenteredCubic.lean** verifies the three-vector formula and the resulting matrix formula for arbitrary finite index sets.

If \(W\) is a centered level space, every \(T\in W\) thus satisfies \(\sum_{ij}T_{ij}^r=0\) for \(1\le r\le3\), when \(n\ge3\). More generally, if \(W\subseteq\mathbb C^s\) has vanishing coordinate power sums for degrees \(1,\ldots,d\), then
\[
 d\,\dim W\le s-1.
\]
Indeed, by taking the coefficient of \(x_1\cdots x_r\) in the power sum of \(\sum x_i w_i\), one gets \(\sum_j\prod_{i=1}^r w_i(j)=0\) for every \(w_1,\ldots,w_r\in W\). Section 1 applies to \(d\) copies of \(W\). For \(s=n^2,d=3\) this bounds \(\dim W\) by \(\lfloor(n^2-1)/3\rfloor\).

In an arbitrary level space the linear coefficient forces the total sum of the entries to be zero. The map recording row and column sums therefore has rank at most \(2n-2\). Its kernel is centered. Consequently, for \(n\ge3\),
\[
 \dim L\le 2n-2+\lfloor(n^2-1)/3\rfloor .
\]
This grows quadratically. For a conjugation-stable complex level space the centered kernel is conjugation-stable, and polarizing the quadratic identity on \(T,\overline T\) gives \(\sum_{ij}|T_{ij}|^2=0\). Thus that kernel is zero and \(\dim L\le2n-2\) for \(n\ge2\).

## 4. An obstruction at every higher degree

The simplest example uses the outer product
\[
 a=(1,-1,0,0),\quad b=(1,\mathrm i,-1,-\mathrm i),\quad T=ab^{\mathsf T}.
\]
All row and column sums vanish. Rotating the columns multiplies \(T\) by \(\mathrm i\) and preserves the permanent. The polynomial \(F(z)=\operatorname{per}(J+zT)\) has degree at most two, because only two rows vary. From \(F(\mathrm iz)=F(z)\), both nonconstant coefficients are zero. Hence \(F(z)=24\) for every complex \(z\). Meanwhile \(\sum_{ij}T_{ij}^4=(\sum_i a_i^4)(\sum_j b_j^4)=8\). **FourthMoment.lean** verifies all these statements using the project's permanent polynomial.

For every integer \(k\ge4\), take \(n=k\), a primitive complex \(k\)th root \(\zeta\), \(a=(1,1,-2,0,\ldots,0)\) and \(b=(1,\zeta,\ldots,\zeta^{k-1})\). Both vectors are centered. The column cycle multiplies \(T=ab^{\mathsf T}\) by \(\zeta\), while \(F(z)\) has degree at most three. Thus \(F(z)=k!\) and
\[
 \sum_{ij}T_{ij}^k=k\bigl(2+(-2)^k\bigr)\ne0 .
\]
For every higher degree, a constant permanent can coexist with a nonzero entrywise power sum of that degree. These examples are one-dimensional. The general rotation criterion, for any number of rows and any admissible scalar, is verified in **RowCoefficients.lean**.

## 5. Limits of constructions based only on symmetry

Suppose a group acts by permuting matrix cells, preserves the permanent, and stabilizes a candidate subspace \(W\). If its action on \(W\) has no nonzero invariant homogeneous polynomials of degrees \(1,\ldots,n\), all nonconstant Taylor terms vanish there. Each coordinate power sum is also invariant. Section 3 with \(d=n,s=n^2\) gives \(n\dim W\le n^2-1\), hence \(\dim W\le n-1\). Examples relying on cancellation of existing invariant terms can fall outside this test.

For finite abelian actions there is a separate counting proof. Choose characters whose nonempty sums, with repetitions, avoid zero up to length \(n\). A cell orbit of size \(s\) affords exactly the characters of the quotient by its stabilizer, once each. If \(A\) is the set of selected characters appearing there and \(B=A\cup\{0\}\), then zero has the unique representation \(0+0\) in \(kB+B\) for \(0\le k<n\). The unique-sum inequality gives \(|(k+1)B|\ge|kB|+|A|\). Iteration gives \(1+n|A|\le s\). Summing over orbits yields the same dimension bound. **CharacterSets.lean** proves the unique-sum inequality in the normalized form used here and the iteration, from the axioms of an abelian group. [Kemperman, *On small sumsets in an abelian group*, Theorem 3.2](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5899-11511_2006_Article_BF02546525.pdf)

## 6. A reduction for spaces containing a full zero-sum row

Suppose \(n\ge2\) and \(L\) contains every zero-sum perturbation in row 1. For \(T\in L\) let \(g_j(T)\) be the permanent of the minor of \(J+T\) obtained by deleting row 1 and column \(j\). Adding any zero-sum vector to row 1 preserves the permanent. Expanding along that row shows \(g_j(T)=g(T)\) for all \(j\). For each fixed \(T\), expansion along row 1 on the whole line gives the polynomial identity
\[
 g(zT)\bigl(n+z\sum_j T_{1j}\bigr)=n!\,.
\]
Two complex polynomials with nonzero constant product must both be constant. Thus the first row of every \(T\in L\) sums to zero and every \(g_j(T)=(n-1)!\). One may subtract the full first row inside \(L\). The remaining space in the other \(n-1\) rows has constant permanent after deleting *any* column. Conversely, the full zero-sum row together with any space satisfying these minor conditions gives a level space. This reduction uses the full-row hypothesis and does not impose such a decomposition on other spaces.

There is also a deletion that preserves all remaining directions. Let \(K_j\) be the subspace of the remaining space supported in column \(j\). After deleting a column \(a\), the spaces \(K_j\) for \(j\ne a\) form independently variable column directions in an \((n-1)\times(n-1)\) level space. Section 2 gives \(\sum_{j\ne a}\dim K_j\le n-2\). Summing this over \(a\) gives \((n-1)\sum_j\dim K_j\le n(n-2)\), hence \(\sum_j\dim K_j\le n-2\). At least two \(K_j\) are zero. Deleting either of those columns is injective on the remaining space.

## 7. A sharp bound when basis matrices each have only two nonzero entries

For \(n\ge2\), any level space admitting a basis of matrices with at most two nonzero entries has dimension at most \(2n-3\). The bound is attained.

The linear coefficient forces every nonzero basis matrix to be a scalar multiple of the difference of two unit entries. If the entries have distinct rows and distinct columns, their product contributes a nonzero quadratic coefficient. Thus each difference lies in one row (horizontal) or one column (vertical).

For any level directions \(H,V\) the mixed coefficient of \(xy\) in \(\operatorname{per}(J+xH+yV)\), divided by \((n-2)!\), vanishes. Inclusion and exclusion of pairs of entries in the same row or column writes it as
\[
 (\textstyle\sum H)(\sum V)-\sum_i R_i(H)R_i(V)
  -\sum_j C_j(H)C_j(V)+\sum_{ij}H_{ij}V_{ij},
\]
where \(R_i,C_j\) denote row and column sums. For horizontal differences in different rows, this reduces to the negative dot product of the two column difference vectors. Sharing one endpoint gives a nonzero term. Sharing both gives two equal nonzero terms. Therefore the sets of columns used by different horizontal rows are disjoint. The transposed assertion holds for vertical columns. For a horizontal and a vertical difference the formula reduces to the product at their intersecting cell, so their supports must be disjoint.

If \(r>0\) rows carry horizontal differences, the horizontal dimension is at most \(n-r\). In each such row the directions sum to zero on its used columns, and the column sets are disjoint across rows. With \(c>0\) active vertical columns the vertical dimension is at most \(n-c\). A family of just one orientation has dimension at most \(n-1\). With both orientations, attaining \(2n-2\) would require one horizontal row using every column and one vertical column using every row. They would share a cell. This proves the upper bound.

To attain it, use all zero-sum vectors on the first row and all zero-sum vectors on the first column outside that row. These contribute \(n-1\) and \(n-2\) dimensions. The mixed quadratic coefficient is zero by the formula above. No matching of size three can be supported on the union of one row and one column. The space is therefore level. The same argument applies to injections from \(m\) rows to \(n\) columns for \(2\le m\le n\), yielding \(m+n-3\). In particular it recovers 6 for this class of spaces in the previous \(4\times5\) assignment.

## Exact finite search

**search_rank_one.py** enumerates ordered pairs of nonzero centered coordinate multisets on the alphabet \(0,1,-1,\mathrm i,-\mathrm i\) for \(2\le n\le12\). For a rank-one direction \(ab^{\mathsf T}\) the coefficient of \(z^k\) is \(k!(n-k)!\,e_k(a)e_k(b)\). This follows by choosing the row and column subsets, matching them in \(k!\) ways and completing each matching. A centered multiset consists of \(r\) opposite real pairs, \(s\) opposite imaginary pairs and zeros, so its elementary symmetric coefficients come from \((1-z^2)^r(1+z^2)^s\). The program also expands the concrete \(4\times4\) example directly over all 24 permutations using exact Gaussian integer arithmetic. Counts are in **search-results.txt**. They describe lines made from this alphabet, with the row and column multisets distinguished. They give no upper bound on the dimensions of general spaces.

## Verification

The four Lean files were checked with Lean 4.36.0 and the project's pinned Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. **lean-check.txt** records the axiom lists. In a checkout of the pinned project with its dependencies built, run `lake env lean /absolute/path/to/FILE.lean` from the project's `lean` directory for each file separately. The proof notes use the splitting theorem cited in section 1 on paper. The Lean checks cover the specific claims identified beside each filename.

The project accepts a proof pull request for the exact posted theorem. These materials document partial results. [Project contribution instructions](https://github.com/brilliant-hq/pequalnp-proofs/blob/main/CONTRIBUTING.md)

