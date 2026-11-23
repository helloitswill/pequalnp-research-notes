# Connected counterexamples of arbitrarily large minimum degree

Fix $d\ge2$ and $m>2^d$. Index $m$ layers by the integers modulo $m$. In each layer $i$ place three centers $c_{i,0},c_{i,1},c_{i,2}$ in a triangle. Add three auxiliary vertices $y_{i,0},y_{i,1},y_{i,2}$. For each color $k$, join $c_{i,k}$ to $y_{i+s,k}$ for every $s$ in
$$ S=\{2^j-1:0\le j<d\}. $$

There are $6m$ vertices and $3m(d+1)$ edges. Each auxiliary vertex has degree $d$ and each center has degree $d+2$. The shifts 0 and 1 give paths from each center to the next center of the same color through a common auxiliary vertex. The triangles connect the three colors. The $3m$ centers form a vertex cover, and the $3m$ edges from shift 0 are a matching. Hence $\tau=3m$.

**There is no four-cycle.** A cycle containing only centers stays within one triangle. With exactly one auxiliary vertex, its two neighbors on the cycle would be distinct centers of the same color, joined by a two-edge path using only centers. That path would lie in one triangle, which has only one center of each color. With two auxiliary vertices, the cycle must alternate between centers and auxiliaries of one color. If centers from distinct layers $i,i'$ shared two auxiliaries, the difference $i'-i$ would have two distinct representations as an ordered difference of elements of $S$.

Every nonzero such difference is unique modulo $m$. Indeed a positive integer difference $2^b-2^a$ with $b>a$ has exact power-of-two divisor $2^a$, and the remaining odd factor $2^{b-a}-1$ determines $b-a$. Negation gives uniqueness for negative differences. All differences lie between $-(2^{d-1}-1)$ and $2^{d-1}-1$, an interval of length less than $m$, so reduction modulo $m$ preserves their distinction. More than two auxiliaries cannot lie on a four-cycle because auxiliary vertices are pairwise nonadjacent.

**Circuit.** In layer $i$, write $x_k$ for the input at center $c_{i,k}$. Compute $h_k$ as the disjunction of the $d$ inputs at its auxiliary neighbors. Use three factors
$$
P=(x_0\lor x_1)\lor(x_2\land h_2),\qquad
Q=(x_0\lor x_2)\lor h_1,\qquad
R=(x_1\lor x_2)\lor h_0 .
$$
Take the conjunction of the three factors. With no selected local center, $P$ is false. With exactly one selected local center $k$, the conjunction equals $h_k$. With two or more selected local centers, it is true because of the triangle. Thus each local output tests precisely the edges of its triangle and the edges to its auxiliary neighbors. Taking the OR of the local outputs covers the entire graph, including assignments in which a selected auxiliary has neighbors in several layers.

Each $h_k$ needs $d-1$ wide binary ORs. The six displayed ORs are also wide because each is true on either of two center singletons. Each layer uses three ANDs. The $m-1$ ORs that combine the layer outputs are narrow because every local output is false on every singleton. Altogether $|A|=3m$, $|B|=(3d+3)m$, and $|D|=m-1$. The circuit has weight $(3d+8)m-2$, while the conjectured minimum $|E|+2\tau-2$ is $(3d+9)m-2$.

For every fixed minimum degree $d\ge2$, the shortfall grows without bound as $m$ increases. The ordinary gate count in this construction is $(3d+7)m-1$, which is $m$ above the candidate unweighted lower bound $|E|+\tau-1$.
