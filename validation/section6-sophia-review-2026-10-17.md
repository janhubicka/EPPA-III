# EPPA-III — Section 6 generalized clique-cover review packet
**Internal collection for Sofia, 17 October 2026. Not sent.**

**Frozen source:** `main-new(20261016-172438).tex`. Former Section 3 is now mainly Sections 5–6. This note does **not** edit, reformat or re-mark the manuscript. The purpose is to preserve a small, prioritized set of author-facing observations until after the interviews next week. The separate, historical correction register is `validation/suggested-corrections.tex`; three source-local patch drafts (S01–S03) were prepared independently.

## Evidence boundary

A green Lean CI run establishes the displayed formal theorem and its declared hypotheses, **not** the original prose in Claims 6.2–6.5 or 6.7–6.10. The Section 6 proof branches are now incorporated into `main` through merged PR #309, with full CI and axiom audit on merged commit `a584870fa30b2721a9b1a7a45f43a750dca62e12` (run 39120421081). Historical PR numbers below identify provenance, not ongoing unmerged dependencies. The lean.yml workflow builds the project, prints all listed theorem axioms, rejects nonstandard axioms and `sorry` placeholders, and runs finite regressions. The exact theorem signatures were independently checked.

| Manuscript target | Checked theorem or module | PR | Latest checked CI |
|---|---|---|---|
| Lemma 6.1, assuming complementary `sK_t` | `eppa_all_positive_clique_double_classification` | #279 | 38954898984, passed |
| Needed stronger equal-clique result, no complementary-half hypothesis | `eppa_noncluster_clique_double_all_positive` | #307 | 39050795207, passed |
| Lemma 6.6 unequal-clique host structure | `transitive_eppa_unequal_two_cliques_and_taylor` | #283 | 38968262355, passed |
| Lemma 6.6 switching sentence | `twoCliqueGraph_switch_to_any_twoClique` | #284 | 38981218830, passed |
| Lemma 6.12, imprimitive C5 | `cycleFive_eppa_imprimitive_models_up_to_complement` | #305 | 39048666466, passed |
| Lemma 6.14, imprimitive R3 | `rook_eppa_imprimitive_models_up_to_complement` | #298 | 39048664918, passed |
| Exceptional Taylor / 2-clique-extension names | `ExceptionalNamedModels.lean` | #306 | 39049550987, passed |

The C5 and rook theorems quantify over genuine EPPA embeddings and genuine invariant nontrivial block partitions. They do not take a prelabelled second half or a coherent family of EPPA lifts as hypotheses. Their results hold up to simultaneous complementation and explicit relabelling of the designated selected copy. Claim 6.15 / 6.16 also have separate axiom-audited certificates (#286 / #293).

## Author comments, ordered by mathematical priority

### S6-01 — **Proof-interface gap**, Proposition 6.17 invoking Lemma 6.1 (priority A)
The printed Lemma 6.1 assumes that the graph induced by `H\G` is another `sK_t`, but Proposition 6.17 uses its conclusion without deriving that hypothesis. Edge-count equality only gives the *number* of edges in the two halves, not the graph isomorphism.

**Repair:** Use the directly verified stronger theorem #307: for every positive `s,t`, a non-cluster, vertex-transitive double-sized EPPA host of the designated `sK_t` is a uniform generalized clique cover or the Wagner exception, **without assuming the outside half is a clique union**. One can (i) replace the old proof of Lemma 6.1 by the compact independent profile argument in `validation/lemma6-1-proposed-proof.tex`, or (ii) add a separate stronger lemma/corollary with that argument before the application. Do not repair merely by saying that regularity makes the outside half isomorphic.

**Most localized alternative (18 October):** retain the existing Lemma 6.1 exactly as written and insert the self-contained complementary-half argument in `validation/proposition6-17-complementary-half-bridge.tex` immediately before invoking it in Proposition 6.17. The proof uses only profile orbit saturation, the true-twin quotient and equality of half-edge counts. This supplies the missing hypothesis `H\G ≅ sK_t` without rewriting Claims 6.2–6.5. The paragraph itself remains proposed source prose until Sofia reviews it.

**Validation:** conclusion Lean-checked #307; exact manuscript prose/placement pending author review.

### S6-02 — **Elementary hypothesis bridge**, Lemma 6.6 and Proposition 6.17 (priority A)
The printed hypotheses say **non-homogeneous** transitive host; the final Lean theorems use **non-cluster** host. The bridge is short and should be stated explicitly.

**Proof:** A finite vertex-transitive disjoint union of cliques has equally sized components. Every partial automorphism sends portions of distinct occupied components to portions of distinct target components. Extend its finite injective map on components to a permutation of all components, and then extend each partial bijection inside a component to a full bijection (equal component sizes). Thus a transitive cluster graph is homogeneous. Contrapositively a non-homogeneous transitive host is non-cluster.

**Validation:** complete paper proof; the one-paragraph, source-local insertion is in `validation/section6-nonhomogeneous-noncluster-bridge.tex`. The generic cluster-to-homogeneous implication is not yet exported as a Lean theorem. This is not an additional classification assumption.

### S6-03 — **Close the named unequal-clique host**, Lemma 6.6 (priority A, short proof)
The machine-checked result gives a canonical Taylor pair pattern with an *optional uniform mate matching*. For `G=K_a \sqcup K_b`, `a,b>=1` and `a!=b`, the exact graph name follows without any group classification.

**Proof:** Let `A,B` be the two base cliques, `n=a+b`, and represent the host vertices by `(i,x)` with `i=0,1`. Put
\[
P=(\{0\}\times A)\cup(\{1\}\times B),\qquad
Q=(\{0\}\times B)\cup(\{1\}\times A).
\]
In the Taylor inter-fibre pattern every pair of distinct vertices in `P` is adjacent, as is every pair in `Q`: same-layer adjacency comes from the two base cliques, and cross-layer adjacency comes exactly from base nonedges. There are no edges between `P` and `Q` except the uniform optional edges `(0,x)(1,x)`. Consequently the host is either `2K_n` or two copies of `K_n` joined by a perfect matching. The first is a cluster graph (and homogeneous), so under the non-cluster hypothesis only the second survives.

**Independent finite check:** `checks/section6_unequal_taylor_named.py` verifies the displayed adjacency identity for **110,000 ordered vertex pairs**, all `1<=a,b<=10`, with and without the mate matching. This is corroboration, not a proof for unbounded orders; the displayed argument is the general proof.

**Validation (18 October):** the actual inter-fibre structure is verified in #283/#309; the all-order named graph identity in #311; the actual-host-to-identity implication in #312; and the exclusion of the mate-free case in #313 (`twoClique_actual_taylor_noncluster_is_matched`). All are merged, with successful full Lean builds and axiom audits. The 110,000-pair finite test remains a secondary regression check. The only remaining manuscript-facing input is the elementary non-homogeneous-to-non-cluster bridge recorded as S6-02.

### S6-04 — **Incorrect wording**, Lemma 6.1 Wagner case (priority A, one deletion)
The displayed Wagner connection matrix is 3-regular; the complement of that graph is 4-regular. Delete “or its complement” directly after the Wagner exception. Complementation of the **pair** `(G,H)`, used elsewhere, is a distinct operation. Confirmed mathematically; #279/#307 formally identify the three-regular canonical model.

### S6-05 — **Graph-name bridge**, Lemma 6.12, C5 degree two (priority B)
Do not identify the two cyclic models without explaining the outside reindexing. The adjacent-pair profile model becomes the Taylor double by shifting the upper labels by `+3 mod 5`; the diagonal-pair profile model becomes the mate-free two-fold blow-up by shifting by `+1 mod 5`, hence the complement of the appropriate 2-clique extension. Both identities and the upper-half bijections are checked in #306. A one-sentence source-local clarification is already prepared as S01.

### S6-06 — **Missing equivariant labels**, Lemma 6.14, R3 degree four (priority B)
The degree-one matching labels cannot be reused at degree four. The actual outside neighbourhoods form an Aut(R3)-invariant multiset of nine 4-subsets. The corresponding subset orbit sizes are `9,9,36,36,36`. Thus the nine profiles exhaust exactly one size-nine orbit, with multiplicity one. **Only then** label outside vertices canonically and compare pair orbits, edge counts and the triangle obstruction. #298 includes this chain, independently of Gardiner and the rank-three classification. Source-local S02 is prepared.

### S6-07 — **Omitted case / unfinished draft marker**, Proposition 6.17 item (4) (priority B)
Preserve the stated alternative “`H` is `2G` or the Taylor double of `G`”. Both `2C_5` and `2R_3` are genuinely non-homogeneous transitive imprimitive EPPA witnesses for the designated homogeneous graph. Proposed source-local S03 fills the unfinished item; do not remove these cases as “homogeneous hosts”.

### S6-08 — **Validation-marker discipline and external inputs** (priority B)
The original Claims 6.2–6.5 and 6.7–6.10 have *not* been Lean-verified sentence by sentence; instead their needed conclusions are certified by independent stronger proofs. Leave their source markers at pending/alternate-proof status until the author's text matches the checked theorem. Do not link a marker pinned to an old `main` SHA to a theorem only existing in an open PR. External Gardiner and rank-three classifications, plus the strict-inequality branch of Proposition 6.17, remain outside the current Lean certification.

### S7-01 — Related generalized covers outside this narrow Section 6 target (priority C)
Lemma 7.9 (“strongly regular generalized clique covers are homogeneous, up to complement”) has a correct conclusion but false individual identifications in its printed argument: `s=1, X=\bar M` gives the complement of `tK_2` for arbitrary `t`, and `t=1, X=Y=1` gives `K_{s,s}`. The elementary common-neighbour proof and a 192-model finite check are in PR #277, `validation/fragile-combinatorial-audit-2026-10-16.tex`. Keep as a separate later author comment; no source edit now.

## Adversarial sign-off boundary

1. **Mathematical combinatorial core:** the equal-clique theorem without an outside-half hypothesis, the unequal-clique Taylor core, the C5/R3 exceptional imprimitive classifications and their finite-model naming identities are integrated in green `main` through #309 and #310; #311 additionally certifies the all-order named two-clique Taylor identity.
2. **Remaining source-level work:** reconcile exact source hypotheses and arguments (S6-01/S6-02), include the short unequal host name proof (S6-03), make the few local corrections (S6-04–07), then update validation markers deliberately.
3. **Not claimed:** the printed proof has been validated verbatim; Proposition 6.17 has been proved independently of the external classifications; the unrelated draft review PR is merged; Gardiner/rank-three classification theorems have been formalized.
4. **Editorial boundary:** collect only. Do not modify the frozen manuscript or send the comments before the author's post-interview review.


## 18 October continuation — repository cleanup and validation boundary

- **Merged:** #276, #277, #278, #309, #310 and #311. Main CI after #309 was green, and #310 separately added the two missing complement-extension axiom-audit entries. The #311 build and axiom audit were green after fixing Lean's `Std.Symm`/`Std.Irrefl` constructor proof syntax; the named two-clique identity holds for arbitrary vertex types.
- **Obsolete PRs:** superseded proof branches were closed with explanations, retaining git history for the unused intermediate lemmas. **This draft #308 is intentionally the surviving author-review packet** and must not be sent or merged before the post-interview review.
- **Active validation:** #312 seeks to turn the exact output of the actual Taylor EPPA witness classification (selected bottom copy + all inter-fibre Taylor adjacency entries + uniform mate bit) into equality with the canonical two-clique matched-double model. Treat this interface as pending until its integrated CI succeeds.
- **Remaining manuscript issues:** the source's missing complementary-half hypothesis in Proposition 6.17 and the non-homogeneous-to-non-cluster bridge still need explicit *paper-level* text. The separate short insertion proposal is `validation/proposition6-17-complementary-half-bridge.tex`. The original Claims 6.2–6.5 and 6.7–6.10 were not certified verbatim; the replacement conclusions are checked independently.
- **External boundary:** Gardiner and the primitive rank-three classification, together with the strict inequality branch of Proposition 6.17, remain classification inputs rather than new Lean theorems. The frozen source is untouched.

- **Further 18 October progress:** #312 passed the full Lean build and axiom audit and was merged. Its theorem `twoClique_actual_taylor_is_matched` proves the actual-host-to-named-model interface for every Boolean two-clique base. PR #313 is validating the final implication that, with the host non-cluster, the mate bit must be present. Once green, S6-03 is machine-certified up to the elementary non-homogeneous/non-cluster input sentence.

- **13th-stage sign-off, 18 October:** PR #313 completed the genuine non-cluster Taylor-host case. CI run 39141779022 was green; the main merge commit is `f754cb61cfb5580271eb2c774f855ae734ab64d2`. It verifies `twoCliqueMatchedGraph_false_is_cluster`, `twoClique_matched_noncluster_forces_mate`, and `twoClique_actual_taylor_noncluster_is_matched` without restricting the two clique sizes. **All actual-host combinatorial ingredients of Lemma 6.6 are now in `main`**; the printed non-homogeneous-to-non-cluster implication remains a short paper proof rather than a generic exported Lean theorem.

- **Final 18 October integration:** #314 recovers a Boolean two-clique representation of the actual selected graph from the verified no-third-component theorem (CI 39142377102), and #315 combines the genuine EPPA host hypotheses, invariant blocks, actual Taylor pair pattern, selected-copy preserving relabelling, and the non-cluster mate exclusion into one result `transitive_eppa_unequal_two_cliques_named_host` (CI 39142690617). Both are merged. This closes the remaining Lean graph-identification interface for Lemma 6.6. The one-way *non-homogeneous and vertex-transitive ⇒ non-cluster* bridge is still elementary manuscript prose, not a newly proved Lean lemma. Gardiner/rank-three classifications remain external as stated.


## 18 October — exceptional Wagner sufficiency check

The necessity theorem identifies a labelled Wagner graph, but this alone does not establish the **reverse implication** that the exceptional graph is an EPPA witness. There is a particularly short independent argument worth retaining: represent the eight-vertex Wagner graph on \(\mathbb Z/8\mathbb Z\) by joining vertices at cyclic distance 1 or 4. The four even vertices induce \(2K_2\) (the two antipodal edges). The subgroup of rotations and reflections preserving even positions has order eight and restricts to the full automorphism group of this \(2K_2\). Since \(2K_2\) is homogeneous, every partial automorphism of the selected graph extends first to an automorphism of the four even vertices, and then to one of these eight symmetries of the Wagner graph. Rotations also establish vertex-transitivity of the whole host.

The explicit canonical coordinates, along with a separate check of all 240 represented partial maps and their extensions within the sixteen dihedral symmetries, are recorded in [PR #320](https://github.com/janhubicka/EPPA-III/pull/320). The Lean certificates `wagnerCanonicalGraph_isEPPA` and `wagnerCanonicalGraph_vertexTransitive` passed the full build, permitted-axiom audit and finite regressions (CI run **39157197778**); PR #320 merged into `main` as commit `77fd46b991e40fc6b6576324a55718d9efa0fd2b`. The alternative PR #321 was closed as superseded. This completes the exceptional *sufficiency* as well as the previously verified necessary classification; it does **not** certify the original source prose sentence by sentence. This remains a proposed author-facing observation, not a change to the frozen manuscript.
