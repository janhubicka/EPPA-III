# Section 6: homogeneity/complement logical bridge (18 October 2026)

**Scope:** frozen manuscript `main-new(20261016-172438).tex`; no changes to author source. The reason to isolate this statement is Proposition 6.17, where the classification may first complement both the selected graph and the host.

* `DoubleCover.homogeneous_complement_iff`: any graph is homogeneous iff its complement is homogeneous. Every partial isomorphism of one is a partial isomorphism of the other; every full graph automorphism is the same automorphism of the complement. No finite-size assumption is needed.
* `DoubleCover.nonhomogeneous_complement_iff`: immediate contrapositive. This ensures that taking complements preserves the manuscript's **non-homogeneous witness** condition, as well as EPPA and vertex-transitivity (already certified in `EPPA/ComplementTransport.lean` and `BlockSystems/TransitiveSeparatedHalf.lean`).

**Distinct bridge not yet Lean certified:** a finite vertex-transitive cluster graph is homogeneous. Each component of a vertex-transitive disjoint union of cliques has equal cardinality. The finite partial isomorphism induces an injective map between the represented components; this extends to a permutation of all components, and the induced partial bijections extend inside each equally sized component. Consequently a non-homogeneous vertex-transitive host is non-cluster, before and after taking complements.

The resulting source-local author comment remains in the separate PR #308. Do not mark the generic cluster-to-homogeneous lemma as Lean-verified until its exact theorem is compiled and axiom-audited. Do not modify the manuscript.

This note should be reviewed together with `validation/section6-nonhomogeneous-noncluster-bridge.tex` on the deferred author-review branch and the closed Proposition 6.17 interface in `validation/proposition6-17-equal-clique-interface.md`.
