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


## Final Lean checkpoint — 16 October 2026

The subsequent stacked PRs have now passed **full Lean CI**, including
`#print axioms`, finite checks, and the placeholder audit:

- [#281](https://github.com/janhubicka/EPPA-III/pull/281):
  `invariant_perfect_matching_yields_pairs`, CI run 38965306130.
- [#282](https://github.com/janhubicka/EPPA-III/pull/282):
  `eppa_case1_perfect_matching_is_taylor_up_to_mate`, CI run 38966111982.
- [#283](https://github.com/janhubicka/EPPA-III/pull/283):
  `transitive_eppa_unequal_clique_actual_host_is_taylor`
  and `transitive_eppa_unequal_two_cliques_and_taylor`,
  CI run 38966405210.

Both actual-host cases therefore lead to the Taylor-pair graph directly;
the selected base is fixed pointwise. The argument neither assumes a
pre-labelled outside half nor uses external Gardiner or rank-three
classification results. An independent finite audit checked 364 unequal
two-clique Taylor graph models and all switched target two-clique
partitions with total order at most seven; this supports, but is not
a replacement for, the general graph argument.

**Scope not yet Lean certified:** the paper assumes that H is
non-homogeneous; the assembled theorems assume that H is non-cluster.
For finite vertex-transitive graphs these are compatible because a
transitive disjoint union of cliques has equally sized components and
is homogeneous, but this elementary bridge has not been separately
packaged as a Lean theorem. The switching-class observation is proved
by the Boolean identity below, not yet as a Lean switching-class theorem.

**Switching proof.** Encode the two cliques by c:V→{0,1}.
For any other two-clique partition d, switch along the set where
c and d disagree. Since adjacency between distinct vertices is
equivalent to equality of the two c-values, after the switch it is
equivalent to equality of the two d-values. Taking d constant yields
K_n. Thus every two-clique partition and K_n belong to the same
switching class.

**Statement note.** The mate-free Taylor double of
G=K_a disjoint-union K_b (a+b=n) is isomorphic to 2K_n and is
homogeneous. Under the lemma's non-homogeneous-H assumption it cannot
actually occur; its inclusion in the statement is mathematically
harmless but redundant. The mate-present graph is two K_n's joined
by a perfect matching.

**Manuscript policy:** the author source remains unmodified.
Claims 6.7–6.10 should not individually be marked as validated verbatim;
the alternative proof certifies their required conclusion. A concise
replacement proof and changelog were prepared separately for author
review.
