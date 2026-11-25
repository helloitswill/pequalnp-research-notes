# Nine tests are necessary and sufficient for 12 items in four groups

Assign a subset A_i of d bits to each of twelve items in four groups of three. For every pair i,j in different groups and every k distinct from them, require that A_k is not contained in the union of A_i and A_j. Then d is at least nine.

Nine suffice. Give the items the twelve affine lines in the plane of order three, represented by the sets of their points among the nine available points. Two other lines meet any given one in at most two of its three points.

For the lower bound suppose that d = 8, padding with unused coordinates if necessary. The twelve subsets form an antichain. Indeed, if A_i is contained in A_j for distinct items, take another item in a group different from j's. The union of those two covers A_i. In particular every A_i is nonempty.

Fix a pivot A. The nine items outside its group have incomparable projections outside A. For two such items i and j, the pair consisting of the pivot and j must fail to cover i, and the pair consisting of the pivot and i must fail to cover j. Four coordinates admit at most six incomparable sets. Consequently every pivot has size at most three.

Suppose a pivot has size three. Its nine outside items give an antichain of size nine in the five remaining bits. Each such antichain consists of all but one of the two-element sets or of all but one of the three-element sets. The accompanying script checks the statement by enumerating subsets in increasing order and extending a prefix only by sets incomparable with all current members.

If these projections are triples, every pair of coordinates is contained in at least one of the nine triples. The projections of the two groupmates of the pivot must each avoid containment in all nine. Each has at most three coordinates, so both equal the omitted triple. Neither has any bit left inside the pivot. Their original codes are therefore equal, contradicting the antichain condition.

If the nine projections are pairs, regard them as the nine edges of the complete graph on five vertices with one edge removed. Each of these nine items has at most one bit inside the pivot. Such a bit gives it one of three colors, and an item with no such bit is uncolored. Partition the nine edges into their three original triples. For differently grouped edges i,j and any other edge k whose two vertices lie in their union, k must have a color distinct from any colors of i and j. Any remaining distinction has to come from inside the pivot. Mark such k as requiring a color and join k to i and j as color incompatibilities. For each of the 280 unordered partitions into triples, the accompanying script exhibits four marked edges that are pairwise incompatible. This requires four colors and exhausts the size-three pivot case.

It remains that all codes have sizes one or two. A singleton code consumes one coordinate which appears nowhere else by the antichain condition. Each two-element code is an edge of a simple graph on the other coordinates. Consider any edge uv with degrees at least two at each endpoint. The edges incident to u other than uv and the edges incident to v other than uv all belong to the same group because any one from each side covers uv. There are at most three of these edges. Hence deg(u) + deg(v) is at most five. Every vertex of degree at least four therefore belongs to a star component, and all other components have maximum degree at most three with no adjacent vertices of degree three.

For any component on s vertices, the number of edges is strictly less than 3s/2. This holds for stars and isolates. On every other component, equality in the maximum-degree-three bound would require a cubic graph, which has adjacent degree-three vertices. A coordinate used by a singleton contributes one code, also strictly less than 3/2. Summing over the eight bits gives strictly fewer than twelve items. This contradicts the required twelve.

Run the finite checks with Python 3.10 or newer.

    python3 -B cross_pairs.py
