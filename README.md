# EPPA-III formalization

Lean formalization and independent validation notes for *Graphs with Small EPPA Witnesses*.

The manuscript is **not edited in this repository** by the formalization workflow.

## Suggested manuscript corrections

The author-facing, source-anchored register is
**[validation/suggested-corrections.tex](validation/suggested-corrections.tex)**.
It distinguishes confirmed errors, proposed localized replacement wording,
paper-level proof repairs, and unresolved dependencies. All entries are
*proposed* until the authors review them; no original manuscript TeX is changed.

The [16 October exceptional-case checkpoint](validation/section3-exceptional-checkpoint-2026-10-16.tex) records current C5/R3 proof boundaries and source-local repairs.

The [general C5 profile dichotomy note](validation/section3-c5-proper-profile-dichotomy.tex) records a stronger orbit-saturation proof that avoids assuming uniform cross-degree.

The [proper-profile C5 outside graph note](validation/section3-c5-proper-outside-cycle.tex) records a conditional direct proof of the complementary five-cycle, and a warning about the primitive Petersen case.

The [empty/full C5 profile proof](validation/section3-c5-empty-full-profiles.tex) handles the last profile alternative in Claim 3.19 and tracks its Lean boundary.\n\nThe [C5 remaining host-case audit](validation/section3-c5-complete-case-analysis.tex) includes reproducible primitive/imprimitive finite certificates and a short list of remaining Lean identifications.

The [canonical C5 matching case](validation/section3-c5-matching-profiles.tex) develops the cross-degree-one proof without assuming any outside labels, keeping the primitive Petersen obstruction separate.

The [canonical matching host graph identification](validation/section3-c5-matching-models.tex) records the two explicit ten-vertex models and the remaining primitive Petersen exclusion.\n\nThe [Petersen primitivity note](validation/section3-c5-petersen-primitivity.tex) gives a one-automorphism proof of the primitive exception in Lemma 3.18, with corresponding Lean certificate.

The [actual-host primitive obstruction note](validation/section3-c5-actual-host-primitive-exclusion.tex) transports the Petersen certificate through the verified matching-host equivalence.

The fuller historical audit remains in
[validation/issues.tex](validation/issues.tex), with a focused
[Section 3 report](validation/section3-rest.tex) and supporting
[finite verification scripts](checks/).

First target: generalised clique covers (Definitions 1.5--1.6, Lemma 3.7 and Claims 3.8--3.11).

Build with `lake update && lake exe cache get && lake build`, and audit with `lake env lean CheckAxioms.lean` followed by `python3 scripts/check_axioms.py axioms.log CheckAxioms.lean`.

A green build validates only the declarations listed in `CheckAxioms.lean`; the manuscript's classification claims remain open until their exact mathematical statements have Lean proofs.
The exact complement-transport theorem is in `EPPAIII/EPPA/ComplementTransport.lean`; it complements both selected graph and host.
