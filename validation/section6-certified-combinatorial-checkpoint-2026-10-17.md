# Section 6 structural validation checkpoint — 17 October 2026

**Authority:** `main-new(20261016-172438).tex` (reorganised Section 6). Author manuscript remains frozen. This note audits *theorems*, not the original proof prose; Gardiner and rank-three classifications remain external inputs.

## Lean-certified combinatorial core

| Manuscript | Exact formal result | Status |
|---|---|---|
| Lemma 6.1, under its stated outside-clique hypothesis | `eppa_all_positive_clique_double_classification` | Green, PR #279 |
| Stronger result required in Proposition 6.17: non-cluster H, no outside-clique hypothesis, all s,t≥1 | `eppa_noncluster_clique_double_all_positive` | Green, PR #307, CI 39050015765 |
| Lemma 6.6, unequal clique sizes, actual host | `transitive_eppa_unequal_two_cliques_and_taylor` | Green, PR #283 |
| Lemma 6.6 switching-class sentence | `twoCliqueGraph_switch_to_any_twoClique` | Green, PR #284 |
| Lemma 6.12, arbitrary transitive imprimitive C5 EPPA host on ten vertices | `cycleFive_eppa_imprimitive_models_up_to_complement` | Green, PR #305 |
| Lemma 6.14, arbitrary transitive imprimitive R3 EPPA host on eighteen vertices | `rook_eppa_imprimitive_models_up_to_complement` | Green, PR #298 |
| Claim 6.15, invariant block size two or nine | `rook_eppa_nontrivial_imprimitive_block_sizes` | Green, PR #286 |
| Claim 6.16, complementary induced rook graph | `rook_eppa_imprimitive_outside_is_rook` | Green, PR #293 |
| Exact Taylor and 2-clique-extension finite graph naming | `ExceptionalNamedModels.lean` | Green, PR #306, CI 39049550987 |

All green cases include a successful full Lean build, axiom audit, finite regressions and unsolved-placeholder rejection. The R3/C5 classifications do not appeal to Gardiner or the rank-three classification.

## Remaining paper-level interfaces

1. **Lemma 6.1 / final Proposition 6.17:** The source Lemma 6.1 assumes `H\setminus G ≅ sK_t`. Proposition 6.17 invokes it without this hypothesis. PR #307 proves precisely the stronger non-cluster theorem for every positive s,t. The manuscript must adopt the alternative direct profile proof (or state and prove a separate stronger lemma) before that invocation is formally justified.
2. **Non-homogeneous ⇒ non-cluster:** In Lemma 6.6 and Proposition 6.17 the printed assumption is that H is *non-homogeneous*; the strongest Lean equal/unequal-clique results use *non-cluster H*. The bridge is elementary: a finite vertex-transitive disjoint union of cliques has equal-sized components and is homogeneous. Keep this sentence explicit; its generic Lean theorem is not yet exported.
3. **Unequal clique named host:** The Lean theorem gives the Taylor inter-fibre graph with uniformly optional mate edges. For `G=K_l ⊔ K_k`, the mate-free host consists of two complete graphs of order `l+k` and is homogeneous; under the non-cluster assumption only the mate-present host remains. It is two complete graphs joined by a perfect matching. This last graph-name reduction is a short paper argument; the exact matched model is not yet one named global Lean theorem.
4. **Proposition 6.17, strict inequality:** `|H|<2|G|` invokes the lower-order rank-three reduction and the classification of imprimitive rank-three graphs. Those are *external* in the manuscript, and not newly certified by the Section 6 Lean work.
5. **Homogeneous selected G:** The Gardiner classification is used as an external theorem. We certify only the combinatorial C5 and R3 witness classifications that follow from it; we do not claim Gardiner's classification is formalized.
6. **Wagner:** The graph of displayed case (2) of Lemma 6.1 has degree 3; its complement has degree 4. Delete the extra “or its complement” after “Wagner graph” in that case. Proposition 6.17 itself already states alternatives up to graph complementation.

## Minimal author-facing source corrections (independent review files)

- **C5 degree two:** Canonical adjacent-pair profiles give the Taylor double after shifting outside indices by 3 modulo 5; diagonal-pair profiles give the complement-of-2-clique-extension model after shifting by 1. PR #306 certifies the graph identities.
- **R3 degree four:** Do not transfer the matching labels from the degree-one case. Instead use the orbit sizes `9,9,36,36,36` of four-subsets, EPPA multiplicity invariance and the nine outside vertices to obtain one complete size-nine profile orbit without repetitions. This canonically labels the outside vertices; only then invoke pair orbit invariance, half-edge counting and the checked triangle obstruction.
- **Proposition 6.17 item (4):** Finish the placeholder as `H is 2G or the Taylor double of G`. The proof already uses this alternative.
- A separate source review ZIP contains three independent diff patches against the exact TeX source; **the TeX is not modified on this branch**.

## Validation markers and merge boundary

Many checked declarations are on unmerged pull request heads. Existing `\leanverifiedat` links use an older pinned `main` commit; do not point green markers at files absent from that pin. Either cite the CI-tested PR head explicitly or advance the repository pin after merging. Mark the complete replacement theorem green only after its manuscript statement/proof have been updated; the *original* Claims 6.2 and 6.4 remain unproved verbatim.

**Next:** once the source-local repairs are accepted, Proposition 6.17 becomes a clean conditional synthesis of externally supplied classifications and the now machine-certified Section 6 combinatorics. Continue with Section 7/8 only after that explicit boundary is recorded.
