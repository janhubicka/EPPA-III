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

The [empty/full C5 profile proof](validation/section3-c5-empty-full-profiles.tex) handles the last profile alternative in Claim 3.19 and tracks its Lean boundary.\n\nThe fuller historical audit remains in
[validation/issues.tex](validation/issues.tex), with a focused
[Section 3 report](validation/section3-rest.tex) and supporting
[finite verification scripts](checks/).

First target: generalised clique covers (Definitions 1.5--1.6, Lemma 3.7 and Claims 3.8--3.11).

Build with `lake update && lake exe cache get && lake build`, and audit with `lake env lean CheckAxioms.lean` followed by `python3 scripts/check_axioms.py axioms.log CheckAxioms.lean`.

A green build validates only the declarations listed in `CheckAxioms.lean`; the manuscript's classification claims remain open until their exact mathematical statements have Lean proofs.