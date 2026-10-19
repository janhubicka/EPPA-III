# Section 5.1 partial two-graph lemma: independent audit (19 October 2026)

**Authority:** supplied `main-new(20261019-085906).tex`, label `lemma:gtg`. **No manuscript edit.** The original path induction does not ensure a previously selected pair exists when the first nonperiodic path is processed. The statement itself remains correct.

## New proof

The source file `validation/section5-partial-twograph-selfcontained-proof.tex` gives a fully self-contained proof. Let `e` be the F₂-valued edge indicator, `D` the domain of a partial two-graph automorphism `f`, and set `δ(x,y)=e(x,y)+e(fx,fy)`. Two-graph preservation gives zero parity on every triple. Anchoring at a single domain point yields a function `h` with `δ(x,y)=h(x)+h(y)`.

For a switching `s`, the compatibility equations reduce to `s(x)+s(fx)=h(x)+c` with one constant `c`. Directed paths never obstruct them. For an even cycle of length 2m, summing the discrepancies of antipodal pairs telescopes and forces the sum of h to be zero. For two odd cycles of lengths a,b, summing discrepancies of the ordered pair under L=lcm(a,b) iterates proves that the two cycle sums agree; L/a and L/b are both odd. Choose c to be their common sum (or zero when no odd cycle). Propagation constructs s on all components, including the first path.

This also supplies a direct proof of the full Mallows–Sloane fixed-graph statement as a special case, so no subtle cyclic hypothesis needs to be imported for Lemma 5.2. **This is a mathematical proof, not yet a complete Lean formalization.**

## Independent finite audit

The new `checks/section5_partial_twograph_cycles.py` verifies the same explicit potential, cycle constraints and constructed switching for *every* partial injection preserving two-graph parity for each anchored graph representative on four and five vertices. It uses a different constructive algorithm from the existing F₂ Gaussian-elimination checker.

- Order 4: 1,672 tested maps, 1,264 preserving triples, 1,132 cycle checks, 176 multi-odd-cycle cases.
- Order 5: 98,944 tested maps, 44,104 preserving triples, 39,856 cycle checks, 6,224 multi-odd-cycle cases.
- All checks passed in local execution. The existing `checks/section5_partial_twograph_audit.py` independently verifies solvability by linear algebra.

These finite checks corroborate the proof; they do not replace the arbitrary-size reasoning.

## Follow-up

1. Lean-certify the generic F₂ triangle-to-potential lemma, then the even/odd cycle equations and the componentwise switching construction. Do not claim the full Section 5.1 lemma as Lean-verified until those are assembled.
2. Audit the true-twin and quotient argument of `lem:fibre-rigidity`, then `lem:2trans`. The source proof has an invariant clique-class counting argument worth formalizing independently.
3. Inspect `lem:second-transversal`, `lem:separation`, and `prop:one-for-all` afterwards. The original printed proof remains frozen.
