# EPPA-III formalization

Lean formalization and independent validation notes for *Graphs with Small EPPA Witnesses*.

The manuscript is **not edited in this repository** by the formalization workflow. The accompanying issue log lives at `validation/issues.tex`.

First target: generalised clique covers (Definitions 1.5--1.6, Lemma 3.7 and Claims 3.8--3.11).

Build with `lake update && lake exe cache get && lake build`, and audit with `lake env lean CheckAxioms.lean` followed by `python3 scripts/check_axioms.py axioms.log CheckAxioms.lean`.

A green build validates only the declarations listed in `CheckAxioms.lean`; the manuscript's classification claims remain open until their exact mathematical statements have Lean proofs.