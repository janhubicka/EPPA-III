# EPPA III §5.1 — completed Lean validation of the partial two-graph switching lemma

**Checkpoint:** 22 October 2026. **Author manuscript frozen:** `main-new(20261019-085906).tex`, label `lemma:gtg`. This is an independent Lean validation of the *statement* by an alternative proof, not a certification of every sentence of the original paper proof. Do not edit or send the manuscript on the basis of this checkpoint without author review.

## Main statements

The following theorems are exported and registered for permitted-axiom checks in `CheckAxioms.lean`.

**Full permutation-restriction interface:**

```lean
EPPAIII.TwoGraphs.partial_two_graph_has_switching_representative
```

For a finite graph `G`, finite domain `D`, and permutation `p` whose restriction to `D` preserves all odd-edge-parity triples of the associated two-graph, constructs a Boolean function `t : V → Bool` such that `p` is a partial automorphism of the induced Taylor transversal `taylorTransversalGraph G t`.

**Source-facing arbitrary partial-injection interface:**

```lean
EPPAIII.TwoGraphs.partial_two_graph_injection_has_switch
```

Starts with **any** function `f : V → V` injective only on `D` and preserving triple parity only on `D`. Uses the finite-domain extension theorem `Equiv.Perm.exists_extending_pair` and returns a Boolean switching `t` on which `f` preserves the induced graph adjacency on `D`. No assumption about `f` outside `D`, no non-homogeneity or EPPA hypothesis, and no external graph classification.

The original empty-domain, fixed-point, even-cycle, odd-cycle and open-path cases are covered uniformly.

## Proof dependency chain

1. **Anchor and discrepancy:** `PartialAutomorphismParity.lean` and `PartialSwitchCoboundary.lean` give the Boolean two-point potential `δ(x,y)=h(x)⊕h(y)` from triple parity, and reduce switching to equations `t(x)⊕t(p x)=h(x)⊕c`.
2. **Paths:** `PartialSwitchPaths.lean` solves arbitrary acyclic constrained arrow systems by source elimination, without relying on any previously selected pair.
3. **Cycles:** `PartialSwitchCycleTelescope.lean` and `PartialSwitchEvenCycle.lean` establish even-cycle zero sums; `PartialSwitchOddCycles.lean` proves odd-cycle agreement by comparing two periods at their product and derives periodicity from ordinary return equations.
4. **Global compatibility:** `PartialSwitchCompatibleConstant.lean` chooses a *single* `c` from an odd cycle if one exists (false otherwise) and verifies compatibility for every closed walk, including repeated traversals.
5. **Finite structure:** `PartialSwitchFiniteCycles.lean` proves every nonempty constrained subsystem either has a source or a removable directed cycle, using finite permutation periods and a cardinality argument.
6. **Glue:** `PartialSwitchCycleClose.lean` proves the omitted final cycle equation from the full XOR sum; `PartialSwitchSourceCycleGlue.lean` performs strong finite-set induction and produces one function `t` satisfying *every* constrained equation.
7. **Final theorem and source interface:** `PartialSwitchFull.lean` assembles the prior theorems, while `PartialSwitchInjection.lean` removes the permutation-restriction presentation.

There is no assumption of coherent EPPA lifts, no Mallows–Sloane theorem invocation, and no local-to-global axiom. Every displayed lemma is backed by a proof term rather than by finite enumeration.

## Review and CI provenance

- Earlier supporting PRs #352–#357: green builds and axiom audits, merged.
- Local cycle closure and gluing PRs #359–#360: green builds and axiom audits, merged.
- Finite source-or-cycle and globally compatible-bit PRs #361–#362: complete green CI for their proof heads, merged.
- Full lemma [PR #363](https://github.com/janhubicka/EPPA-III/pull/363): green full CI [run 39690185917](https://github.com/janhubicka/EPPA-III/actions/runs/39690185917), merged.
- Arbitrary injection [PR #364](https://github.com/janhubicka/EPPA-III/pull/364): green full CI [run 39691199183](https://github.com/janhubicka/EPPA-III/actions/runs/39691199183), merged.
- Integrated `main` merge: `0ae6b3e883ead1e6fa77188e54bf62937d5723e4`. Its full workflow [run 39691798823](https://github.com/janhubicka/EPPA-III/actions/runs/39691798823) **completed successfully** on the integrated main commit, including the full Lean build, permitted-axiom audit, finite regressions and placeholder rejection.

The project workflow builds Lean, prints axioms of named declarations, rejects nonstandard axiom dependencies and unsolved placeholders, and runs independent finite regressions.

## Manuscript / authors' review boundary

The standalone proposed alternative proof is `validation/section5-partial-twograph-selfcontained-proof.tex`. It is consistent with this Lean proof architecture and avoids the original path induction's missing previously selected pair in the first open-path case. The old checkpoint `validation/section5-partial-switch-checkpoint-20261021.md` records earlier pending obligations as they stood at that date; this note **supersedes its pending theorem status**, without rewriting the historical record.

**Validation label policy:** mark `lemma:gtg` as `statement verified via alternative Lean proof` only after manuscript authors approve the corresponding proof-marker update. Do not mark the original source proof prose as verbatim validated. No author TeX has been modified. The separate Sofia Section 6 review packet PR #308 stays unmerged and unsent.
