# Icosahedral and Johnson Taylor witnesses

Let $Q(G)$ be the two-graph of odd-edge triples in $G$. For $r\in V(G)$, switch at $N_G(r)$ and delete $r$. The resulting graph $D_r$ satisfies
$$
xy\in E(D_r)\quad\Longleftrightarrow\quad \{r,x,y\}\in Q(G)
$$
for distinct $x,y\ne r$. This formula makes the descendants equivariant under two-graph automorphisms. A graph automorphism of $D_r$ extends by fixing $r$, since $D_r\sqcup K_1$ represents $Q(G)$.

If $Q(G)$ is homogeneous, homogeneity applied to the singleton or the two-point domain gives a transitive action on points and on ordered pairs of distinct points. The point stabilizer extends every partial automorphism of $D_r$ by adjoining $r$ to its domain. Conversely, vertex transitivity together with homogeneity of one descendant suffices. For a nonempty partial map, first move its chosen domain point to its specified image. The remaining map fixes the chosen point and is a partial automorphism of its descendant. Extend that map there and compose with the first automorphism.

If both triple parities occur, every pair of distinct points has an odd and even extension by the transitivity on ordered pairs. For each $r$, apply this to a pair $r,x$ to get both an edge and a nonedge of $D_r$. If $D_r$ is a union of cliques, the ends of an edge have identical adjacency to every other vertex of $D_r$ and to the isolated $r$. Every triple through this pair is odd. If $D_r$ is complete multipartite, the ends of a nonedge have identical adjacency outside the pair, so every triple through that pair is even. Both possibilities contradict the two parity extensions. Gardiner's finite homogeneous graph theorem leaves $C_5$ and $R_3$, using their self-complementarity. Thus $|V(G)|=6$ or $10$, and $G$ is switching-equivalent to $C_5\sqcup K_1$ or $R_3\sqcup K_1$, respectively.

The Taylor double is unchanged under switching up to the explicit relabelling that exchanges the two vertices of each switched fibre. A relabelling of the base lifts using the same relabelling in each layer. The exact host identifications in the Python check use the following coordinates.

- For the icosahedron, one layer consists of the north pole and the lower pentagonal ring in cyclic order. The other layer consists of their antipodes in matching order. The program checks the 12-point bijection against the two-ring adjacency relation, including the connections between the rings.
- For $J(6,3)$, begin the first layer with $\{0,1,2\}$. Its remaining nine points are the 3-sets containing $i\in\{0,1,2\}$ and excluding $k\in\{3,4,5\}$, with their other two members drawn from $\{3,4,5\}$. These points have intersection of size two exactly when the distinct index pairs agree in one coordinate. The second layer consists of the complements of the 3-sets in corresponding order, which gives the Taylor adjacency across the layers.

The program enumerates $2^5$ switch choices for the six-point model with the root bit fixed. The graph types are $C_5\sqcup K_1$, its complement, the legged triangle, and its complement, with counts $6,6,10,10$ on the fixed labels. For the ten-point model it checks a switch and vertex bijection to the Petersen graph on the 2-subsets of a five-point set, with disjointness as adjacency. These suffice to identify the printed switching classes.

The searches find 60 and 720 two-graph automorphisms, respectively, and verify point transitivity. The script verifies homogeneity of $C_5$ and $R_3$ by point movers. For each pair $x,y$, an automorphism sends $x$ to $y$ and fixes each other vertex at which their adjacencies agree. The resulting one-point extensions imply homogeneity by induction on the domain. Together with the descendant criterion and the all-transversal theorem, this proves EPPA for the canonical embeddings.

For the same result at each actual embedding, consider any copy $G'$ of a graph in the indicated switching class inside its named host. The exact checks confirm that every pair of points of either class has an even triple extension. A pair of Taylor mates is nonadjacent and every other vertex is adjacent to exactly one mate, so such a pair has no even triple extension within any induced subgraph of the host. Consequently the copy uses at most one vertex of each fibre. The orders 6 and 10 then force it to be a transversal. This permits the all-transversal theorem at the prescribed embedding, and simultaneous complementation gives the complementary formulations.

The Python program uses exact Boolean computations and no external solver. The descendant argument reduces homogeneous two-graph recognition to Gardiner's theorem without a computational assumption.
