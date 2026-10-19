# Section 5.2 one-for-all argument — adversarial audit, 19 October 2026

**Manuscript:** `main-new(20261019-085906).tex` (`lem:second-transversal`, `lem:separation`, `prop:one-for-all`). **Frozen: no author-source changes.**

## Audit of the logical chain

**Second transversal:** Non-homogeneity supplies a partial automorphism of the selected graph that does not extend inside that graph. EPPA lifts it to an automorphism h of the Taylor double. Once fibre rigidity is established, h sends the natural transversal to a transversal T_S. The image cannot be T_empty (that would extend the partial map inside G) or T_X (the nonempty partial domain is sent from selected vertices to selected vertices). Thus S is nonempty and proper, and conjugating extensions proves EPPA for T_S. This argument is sound conditional on the *full* fibre-rigidity lemma.

**Separation:** Every automorphism α of the two-graph has a fibre-preserving Taylor-double lift (the full-automorphism case of the switching lemma). Under the 2-transitive action, send one chosen point of S to a and one outside S to b. The two transported EPPA transversals have switching labels c and c+1_{α S}. Since the indicator of α S differs at a and b, one of these transversals separates them. The elementary Boolean implication is `one_of_two_switchings_separates`.

**One-for-all:** Suppose f:A→B is a minimal nonextendible two-graph partial automorphism. Since Aut(Δ) is 2-transitive, |A|≥3. Remove a∈A and compose f with the inverse of an automorphism extending f on R=A∖{a}; now f fixes R and maps a to b outside A. For each r,s∈R, equality of triple parity of {a,r,s} and {b,r,s} gives
\[
 e(a,r)+e(a,s)=e(b,r)+e(b,s)\pmod2.
\]
Thus r↦e(a,r)+e(b,r) is constant, yielding either identical or complementary types over R. The generic Boolean lemma `types_equal_or_complementary` certifies exactly this dichotomy. The identical case is already a partial automorphism of G and extends by EPPA. In the complementary case, choose an EPPA transversal with switching labels t(a)≠t(b). Then
\[
 e_t(a,r)+e_t(b,r)=1+t(a)+t(b)=0,
\]
so the same single-point partial automorphism extends on that transversal. Fibre rigidity descends either host extension to an automorphism of Δ, contradicting minimality. The Lean lemmas `complementary_types_equal_after_switch` and `complementary_types_equal_after_switch_on` certify this switching calculation.

**No counterexample or additional hypothesis gap was found** in these three paper arguments once their named dependencies are granted. The Boolean proofs are independent of all external graph classifications.

## Certification boundary

- PR on this branch formally verifies **only** the finite-switching Boolean implications and the all-domain type dichotomy. It does not yet formalize the theorem-level orbit lifts, EPPA transfer to a new transversal, or minimal-partial-automorphism induction.
- The first missing upstream theorem is the EPPA/true-twin argument proving the even-triple pair coverage in Lemma `lem:fibre-rigidity`. The graph-distance consequence is checked in the merged Taylor distance PR.
- The next global theorem is the exact induced fibre action and 2-transitivity statement `lem:2trans`. This supplies the group-action hypotheses for the separation and one-for-all arguments.
- Do not mark the whole `prop:one-for-all` Lean-verified until these interfaces and the final assembly compile.

**Preferred editorial route:** retain the existing concise proof of the one-for-all proposition; no prose replacement appears necessary. The only Section 5 proof replacement presently recommended is the self-contained parity proof of `lemma:gtg` in `validation/section5-partial-twograph-selfcontained-proof.tex`.
