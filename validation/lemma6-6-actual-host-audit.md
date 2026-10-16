# Unequal clique sizes — Section 6, Lemma 6.6 (16 October 2026)

The present manuscript `main-new(20261016-172438).tex` assumes a non-homogeneous, vertex-transitive, imprimitive EPPA host of exactly twice the base order. The Lean cases were previously scattered across `UnequalCase1FromDegrees`, `UnequalCase2Taylor`, `UnequalCase2Triangle` and `UnequalThreeComponents`.

## New certified interface (subject to passing CI)

`transitive_eppa_unequal_clique_actual_host_dichotomy` combines the actual-host cases from **an arbitrary nontrivial invariant block map**, with no pre-labelled outside half: (i) exactly two complete host blocks, with a perfect cross-block matching; or (ii) a canonically labelled Taylor double with uniformly optional mate matching. It derives block size bounds, their uniformity, a selected edge, the needed `co-P3` witness, and base non-homogeneity directly from unequal clique degrees.

`transitive_eppa_unequal_two_base_components` strengthens the exclusion of three components to an explicit exhaustion: for any vertices x,y of unequal base degree, every z lies in the clique component of x or y. This gives the source conclusion s=2 without relying on the manuscript's informal action on selected block labels.

## Remaining assembly obligations

- Source Lemma 6.6 assumes **non-homogeneous H**, whereas the Lean case theorems use **non-cluster H**. Derive the latter from vertex transitivity plus the elementary fact that a transitive cluster graph is homogeneous. Do not silently assume this bridge.
- Case 1 currently says *two clique host blocks with a perfect matching*, but does not yet export a canonical isomorphism to the manuscript's named graph `2K_n` plus the matching. The elementary graph-model identification should be formalized before marking the full lemma green.
- Case 2 has a strong already-verified labelled Taylor-pattern theorem. Its mate edges may be uniformly present or absent; this must not be dropped.
- The switching-class statement in the last sentence of Lemma 6.6 is elementary and has not yet been formally certified.

No manuscript TeX is changed. The source corrections should be as local as possible; a paper-level audit of the above gaps follows the Lean CI result.
