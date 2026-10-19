# Section 5: induced fibre action and 2-transitivity (19 October 2026)

**Manuscript:** frozen `main-new(20261019-085906).tex`, lemma `lem:2trans`.

The source's 2-transitivity conclusion admits a slightly more general formulation:

> Let G be a finite non-homogeneous graph, H a graph with the designated induced EPPA embedding of G into the lower layer of Bool×V(G), and suppose every H-automorphism preserves the natural two-point fibres. Then the induced permutations of V(G) act 2-transitively.

The proof uses only EPPA and fibre invariance, not the specific Taylor adjacency or the nontriviality of its associated two-graph. The latter are needed upstream only to *prove* fibre invariance and downstream to identify the induced group with Aut(Δ).

1. The already Lean-audited theorem `eppa_maps_two_fibres` transports any ordered selected edge to any ordered selected edge, and similarly for ordered nonedges, by a genuine automorphism of H fixing the selected images.
2. The new theorem `eppa_induced_pair_orbit` obtains its induced permutation on V(G) explicitly from the invariant pair system.
3. If every induced permutation preserved adjacency of G, an EPPA extension of every partial automorphism would induce an actual automorphism of G extending it. That makes G homogeneous, contradiction. This implication is the new `induced_action_not_all_graph_automorphisms`; the equivalent existence of a changed adjacency-status pair is `induced_action_changes_some_pair_type`.
4. The induced permutations form a group (under composition and inverses), and thus one such edge/nonedge mixing permutation merges the two previously transitive ordered-pair orbits. The resulting group is 2-transitive. **This last group-composition assembly is not yet an exported Lean theorem.**

In the source proof, the argument for equality with Aut(Δ(G)) remains distinct: every H-automorphism preserves the induced triangle types because the fibres are intrinsic, and every automorphism of Δ lifts to H by the (full-domain case of the) switching lemma.

**Status discipline:** The algebraic and pair-orbit ingredients are formalizing on this branch, subject to CI; do not mark `lem:2trans` fully machine-verified until the final assembly and the EPPA→intrinsic fibres implication are also certified. No author-source changes are made here.
