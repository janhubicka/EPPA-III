# EPPA III — Proposition 6.17 proof-interface audit, 28 October 2026

**Author-source policy:** The manuscript is frozen. This note only records verified theorem interfaces and proposed local repairs; it does not edit the paper, send comments to Sofia, or merge her separate review packet [PR #308](https://github.com/janhubicka/EPPA-III/pull/308).

**Source-version boundary:** The numbering refers to Proposition 6.17 and its preceding Lemmas 6.1, 6.6, 6.12, and 6.14. The recent author-review copy `main-new-rehurek-current.tex` has a shorter Case (4) than the earlier reviewed draft; both should be reconciled against the authoritative frozen source before patches are applied.

## Results already certified in Lean

1. **No outside-half assumption in the equal-clique case.** `CliqueCovers.eppa_nonhomogeneous_clique_double_all_positive` applies to any non-homogeneous, vertex-transitive double-sized EPPA host of `sK_t` (`s,t>0`), yielding a fixed-base generalized clique-cover model or the Wagner exception; **PR #367 merged**, CI green. It replaces the logically invalid invocation of the printed Lemma 6.1 (which assumes that the complementary half already induces `sK_t`).
2. **Non-homogeneous transitive hosts are non-cluster.** `BlockSystems.transitive_nonhomogeneous_not_cluster` follows from uniform closed-neighbourhood quotient fibres and explicit extension of partial maps of equal-sized cliques; **PR #366 merged**, CI green. No classification input.
3. **Unequal-clique named host with the printed non-homogeneous hypothesis.** `BlockSystems.transitive_eppa_unequal_two_cliques_named_host_nonhomogeneous`, **PR #367 merged**, CI green, supplies the matched-double conclusion under the actual invariant block hypotheses.
4. **Complemented clique unions.** `CliqueCovers.eppa_nonhomogeneous_complement_clique_double_all_positive`, **PR #368 merged**, CI green, complements both the selected graph and its EPPA host, transports transitivity and non-homogeneity, and classifies the complemented host up to the same cover/Wagner alternatives. This does **not** invoke Lemma 5.12 outside its hypotheses.
5. **Disjoint doubles of homogeneous graphs.** `BlockSystems.disjoint_double_counterexample_schema` proves that a homogeneous base containing an induced `P_3` has a vertex-transitive, non-homogeneous, genuine EPPA disjoint double; **PR #369 merged**, Lean/axioms green. If the base is connected, `BlockSystems.disjoint_double_imprimitive_counterexample_schema` additionally gives a nontrivial Aut-invariant two-block partition by connected components; **PR #370 merged**, Lean/axioms green.

## Additional proof branches — status must be checked before citing as completed

- [PR #371](https://github.com/janhubicka/EPPA-III/pull/371): explicit `2C_5` counterexample with a finite dihedral homogeneity certificate, connectedness, induced `P_3`, and actual imprimitivity. **Pending CI/merge.**
- [PR #372](https://github.com/janhubicka/EPPA-III/pull/372): **merged, green**. An imprimitive rank-three ordered-pair action gives a cluster/co-cluster host; vertex transitivity makes it homogeneous. This eliminates the separate classification of imprimitive rank-three graphs, but not the earlier small-witness-to-rank-three theorem.
- [PR #374](https://github.com/janhubicka/EPPA-III/pull/374): **merged, green**. Extracts the necessary same-block and different-block witnesses from the actual finite invariant block hypotheses (surjectivity, two block labels and a block of size at least two), and certifies the strict-order rank-three contradiction with those hypotheses.

## Minimal author-facing changes, in priority order

**P617-01 (hypothesis mismatch):** In the equal-clique paragraph of the proof, do not say the existing Lemma 6.1 alone establishes the generalised clique-cover conclusion. Its assumption on the other half is not derived. Either replace Lemma 6.1's proof with the shorter independent profile argument in `validation/lemma6-1-proposed-proof.tex`, or insert a separate strengthened corollary using that argument. Lean certifies the stronger conclusion via #367, **not the printed proof verbatim**.

**P617-02 (host non-homogeneity):** Insert the elementary bridge: a finite vertex-transitive cluster graph has equally sized complete components and is homogeneous. Hence the assumed non-homogeneous vertex-transitive host is non-cluster. This is now verified by #366 and should not remain an implicit change in hypotheses.

**P617-03 (complement of clique unions):** Replace the invocation of Lemma 5.12 on `G ≅ \overline{sK_t}` by complementing the EPPA pair and applying the strengthened equal-clique classification (as formally validated in #368). The original lemma explicitly excludes this class.

**P617-04 (do NOT discard 2G):** The proof's assertion that `2C_5` and `2R_3` are homogeneous hosts is false: whenever a connected homogeneous base `G` contains an induced `P_3`, its disjoint double `2G` is transitive, imprimitive, EPPA, and **non-homogeneous** (#369–#370). Retain `H=2G` in the homogeneous-base alternative, along with the Taylor double. This is a mathematical omission, not merely a relabelling issue. The fully explicit C5 certificate is being separately checked in #371.

**P617-05 (R3 list):** The `R_3` item in the recent author-review copy omits the complement of the two-clique extension of `R_3`, although the preceding lemma includes it. **PR #375 is merged and Lean-verified:** its canonical mate-free blow-up has nonadjacent false twins, while the Taylor double has none. Both are 8-regular but cannot be isomorphic. Reinstate the missing alternative explicitly.

**P617-06 (Wagner wording):** Delete “or its complement” immediately after the 3-regular Wagner model in the statement of Lemma 6.1. The complement is 4-regular; simultaneous complementation of the *pair* of graphs in the final theorem is a separate operation.

**P617-07 (strict-order branch):** The argument `|H|<2|G|` still uses the earlier small-EPPA-witness proposition to obtain the rank-three alternative. The follow-up imprimitive rank-three step is now certified by PR #372, and the contradiction from the manuscript's exact block cardinalities by PR #374, both merged and axiom-audited. No imprimitive rank-three *classification* is needed, but the earlier small-witness proposition remains a dependency.

## What is not certified here

- The Gardiner classification of finite homogeneous graphs (reducing the base `G` to its named families), and the earlier small-order EPPA-witness-to-rank-three theorem, have not been replaced by Lean proofs here.
- PR #371, the concrete finite C5 homogeneity and `2C5` instantiation, is still under CI; do not mark that optional concrete certificate as completed. The abstract disjoint-double theorem and invariant-block system were already certified in PRs #369–#370.
- The original text of Claims 6.2–6.5 and 6.7–6.10 has not been checked verbatim. Relevant conclusions have stronger independently formalised replacements.
- No existing source validation marker should be silently changed to “original proof checked” on the basis of these alternative certificates.
- The introduction's low-order two-graph equivalence issue remains separate.
