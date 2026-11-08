# EPPA III — corrected two-cover obstacle theorem (8 November 2026)

**Frozen manuscript:** `main-new(20261031-234151).tex`, item `item:taylorobstacle` of `thm:obstacles`. This is a review note, not an edit of the author's TeX. Previously withdrawn/commented annotations are untouched. The unrestricted original statement is false.

## Conditional theorem

Let `H` be a two-fold cover of `K_X` with independent pair-fibres `F_x={(0,x),(1,x)}`, a perfect matching between any two distinct fibres, and the global deck involution. Assume:

* every automorphism of `H` preserves the fibre partition;
* `H` is an EPPA witness for each full transversal (one vertex per fibre).

Then for **every selected vertex subset** `S` the following are equivalent:

1. `H` is EPPA for the induced graph `H[S]`;
2. `S` contains no full fibre together with a vertex outside it;
3. `S` meets each fibre in at most one point, or `S` consists of exactly one full fibre.

Every forbidden triple induces `K2 + K1 = complement(O3)`, with one nonedge equal to a fibre pair. Note that this is a property of **the embedding**, not just the abstract graph type.

**Proof.** A full fibre `{u,u'}` plus a vertex `z` from another fibre has exactly one edge to `z`; say `u'` is nonadjacent to `z`. The partial isomorphism `u -> z, u' -> u'` maps one independent pair to another but cannot extend, as it sends a fibre pair to a non-fibre pair. Conversely, any subtransversal extends to a full transversal; EPPA is hereditary for induced selections. A complete fibre induces an independent pair; its swap is extended by the global deck involution.

For `|X|>=2`, inclusion-maximal EPPA selections are exactly the `2^|X|` full transversals **and** the `|X|` full two-point fibres. The minimal forbidden selections are the `2|X|(|X|-1)` triples above. For `|X|>=3`, only full transversals are large enough to have at least half of the vertices. Thus the original concluding claim that *all* maximal EPPA selections are transversals is false even for the icosahedron and `J(6,3)`.

## Supplying the assumptions

The existing Lean theorem `EPPAIII.TwoGraphs.homogeneous_two_graph_all_transversals_eppa` establishes the second hypothesis for any Taylor double associated with a homogeneous two-graph. The first must be checked separately; the natural antipodal fibres of the icosahedron and `J(6,3)` are the unique distance-three mates, and hence invariant under graph automorphisms.

Neither condition may be dropped:

* `2 K4` is homogeneous, so all induced selections have EPPA, but the canonical displayed pairs are **not** invariant.
* The Taylor double of `C5` is vertex-transitive and has invariant pairs (each vertex has a unique zero-common-neighbour mate), yet the transversal `{(0,0),(0,1),(1,2)}` induces a `P3` whose two edges have one and two common neighbours in the host. The partial automorphism swapping the leaves cannot extend.
* The Taylor double of `K2 + 3K1` is not vertex-transitive: its vertices have 3 or 1 incident triangles. A two-vertex selected induced subgraph already fails EPPA.

## Finite audit

The separate standard-library regression checks all selected subsets and all partial graph isomorphisms of the crown graphs on 6 and 8 vertices, against their explicit full groups of orders 12 and 48. It finds respectively `2^3+3=11` and `2^4+4=20` maximal EPPA subsets, and verifies the stronger `C5` counterexample. Optional independently-run named-example scripts check the icosahedron (`735` eligible subsets, `60` forbidden triples) and `J(6,3)` (antipodal fibre structure).

**Boundary:** theorem is paper-verified under the two explicit hypotheses, and the all-transversal implication is a previously verified Lean theorem. The complete obstruction equivalence has *not* yet been formalized as one Lean declaration. Do not mark the original unrestricted clause green. The `T(4)` issue is independent and requires the separate `n>=5` statement correction; the `R4`, Clebsch, and Schläfli clauses have their own finite certificates.
