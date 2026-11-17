# Triangular witnesses in Section 4

## Incorrect statement and counterexample

The hypothesis of `thm:triangularsubgraphs` permits the selected graph to be isomorphic to the line graph of a triangle-free graph. The proof requires triangle-freeness of the edge set in its given embedding.

In `T(8)`, select the triangle on points 1, 2 and 3 and the three-edge star with centre 4 and leaves 5, 6 and 7. The induced graph on these six edges is `2K₃`, which is also the line graph of two disjoint three-edge stars on eight points. Exchanging the two components defines a partial automorphism. A star triangle lies in a clique of size seven in `T(8)). A triangle formed by the three edges of a root triangle is maximal and has size three. The exchange therefore cannot extend. The amended hypothesis refers to the graph on the host's underlying points whose edges are the selected vertices.

The earlier triangle distinction and size remark also need the range `n ≥ 5`. For `n = 4`, complementation of the two-subsets is a host automorphism and swaps the two types of triangles. The whole graph `T(4)` is the octahedral graph. It is homogeneous, and its selected root `K₄` contains a triangle and has six edges, exceeding the claimed bound of four. The restriction to five or more points is already present in the triangular case of the main theorem.

## Small proof correction

In the proof of sufficiency, an intersection of at least two selected edge sets has size one **if and only if** they form a focused clique. The converse is used in the next sentence. The patch adds it explicitly.

## Relation to the classification theorem

For the abstract description in the main theorem, suppose the selected graph is the line graph of a triangle-free graph. Each triangle of the selected graph then corresponds to three edges sharing a point. A fourth edge adjacent to exactly two of these three would have to join the two corresponding leaves, producing a root triangle. Hence the selected graph has no induced four-vertex diamond. In the actual root given by the embedding, an edge joining a vertex of a triangle to an outside vertex would give a diamond on the four edges. Every root triangle is therefore a component.

If there are `r ≥ 1` such components, Mantel's theorem bounds the total edge count by `3r + floor((n−3r)²/4)`. The expression without the floor is convex in `r`, so its maximum is at an endpoint of `1 ≤ r ≤ floor(n/3)`. The two endpoint bounds are strictly below `n(n−1)/4` for `n ≥ 5` (for the second endpoint use the bound `n` for `n ≥ 6`, and check `n = 5` directly). Thus the main theorem's half-order bound resolves the embedding ambiguity. The patch changes the local statement and its proof.

The lattice statement has the same embedding issue, and its unrestricted wording is false already at `n = 3`. The graph `G = T(3) = K₃` has three vertices, attaining the stated threshold. It is a claw's line graph, but every `L(r,s)` with `r+s ≤ 3` has at most two vertices. The proof needs the triangle-free graph on the actual `n` points to use its bipartition inside `T(n)`. The patch makes that hypothesis explicit. The preceding sentence is changed to match it.

In the half-order corollary, the short diamond and Mantel argument justifies passing from the abstract hypothesis to the amended sufficiency theorem. For necessity at `n = 5`, the mixed-triangle obstruction bounds every root degree by two if there is a root triangle. The triangle then uses three of the five points and forms a component. At most four edges in total are possible, so a half-order selected graph cannot have such a root triangle. This replaces the computational sentence in that case.
