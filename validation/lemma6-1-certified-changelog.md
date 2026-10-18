# Lemma 6.1: certification and localized manuscript update

**Source:** `main-new(20261016-172438).tex`, `\label{thm:sKt_witnesses}`. The author manuscript remains unchanged.

## Verified theorem

`EPPAIII.CliqueCovers.eppa_all_positive_clique_double_classification` in `EPPAIII/CliqueCovers/AllParametersClassification.lean` proves the full result for all **positive** (s,t). It assumes:

- a fixed induced EPPA embedding of (sK_t) into (H);
- (|H|=2st), vertex-transitivity of (H);
- an actual equivalence identifying the complementary induced graph with (sK_t), as in the manuscript.

It proves either a uniform generalized clique-cover normal form with the selected embedding fixed pointwise, or the (s=t=2) Wagner model. No imprimitive hypothesis, no Gardiner classification, no rank-three classification, and no coherent choice of extension automorphisms is required.

The proof is assembled from the checked noncluster profile orbit theorem, the cluster cross-block matching theorem, the (t=1) independent-base theorem, and the (s=1) theorem by graph complementation and reindexing. The Wagner branch uses dependent index casts to express exact alignment under (s=t=2).

## Adversarial review

1. **Original Claims 6.2–6.5 are not Lean-certified verbatim.** Their conclusion is certified by the direct profile proof. In particular, no unjustified stabilisation of an outside clique or simultaneous matching-coordinate normalization is used.
2. **The complementary-half assumption matters for cluster hosts.** Example: (H=4K_3) extends an induced (G=3K_2) of half its order, but its outside half is (K_3\dot\cup 3K_1), not (3K_2).
3. **The source's exceptional clause needs one localized correction:** delete “or its complement” after “Wagner graph”. The displayed matrix is 3-regular and cannot give the 4-regular graph complement.
4. The source's imprimitive assumption may be retained for consistency; it is unnecessary for the verified classification.
5. Avoid marking Claims 6.2–6.5 green individually. Only Lemma 6.1 is fully supported by the complete Lean theorem.

## Author-facing proof

`validation/lemma6-1-proposed-proof.tex` is a self-contained, compact replacement for the **proof only** of Lemma 6.1, preserving the notation (C_i,D_j,P(w),X,Y,M,\overline M). Keep the statement but delete “or its complement” in case (2). It introduces no external classification.

## Verification

The original all-parameter branch head `70c2ea6e850eb43f8f2d3d3cdab446b7409727e3` passed the full GitHub Actions Lean build, `#print axioms` audit, finite matrix and Section 3 regression checks, and placeholder rejection on run `38954186431` (16 October 2026). The proof and definitions here are transplanted unchanged onto the current PR #278 base for review.
