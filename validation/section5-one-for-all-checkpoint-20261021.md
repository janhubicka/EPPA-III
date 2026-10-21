# Section 5 — Proposition 5.11 theorem-validation checkpoint (21 October 2026)

**Author manuscript:** frozen `main-new(20261019-085906).tex` (and the correspondingly numbered `main-new(3).pdf`). **No source editing or correspondence with Sofia.** This checkpoint records theorem-level verification using an alternative concise proof; it does not certify every line of the manuscript proof.

## Verified result

For every finite graph `G` with a designated induced EPPA embedding into its **canonical Taylor double** `H`, if `G` is non-homogeneous, then:

1. Its associated odd-edge-parity two-graph is homogeneous: **every partial two-graph automorphism extends to a full automorphism**.
2. Every switching representative `G_t`, for **every Boolean side choice** `t : V(G) → Bool`, admits an EPPA embedding into the *same* Taylor double `H`, via `x ↦ (t(x),x)`.

These are exactly the two conclusions of **Proposition 5.11**. The Lean representation of finite partial maps as restrictions of full permutations is equivalent to the ordinary partial-bijection definition on finite sets. The closed-twin quotient typeclass instances in the source-facing theorem are standard finite/decidable structure, not extra graph-theoretic hypotheses.

### Source-facing exported certificates

- `EPPAIII.TwoGraphs.taylor_eppa_two_graph_homogeneous_all_cases` — all orders and both trivial/nontrivial two-graph cases, **PR #348**, passed [CI 39568084382](https://github.com/janhubicka/EPPA-III/actions/runs/39568084382) and merged.
- `EPPAIII.TwoGraphs.taylor_one_eppa_all_switching_transversals` — all switched induced graphs with the genuine designated transversal embeddings, **PR #350**, passed [CI 39569798832](https://github.com/janhubicka/EPPA-III/actions/runs/39569798832) and merged.
- `EPPAIII.TwoGraphs.homogeneous_two_graph_all_transversals_eppa` — reusable theorem: homogeneity of the two-graph alone forces every canonical transversal to be EPPA for the Taylor double.

The complete proof chain is axiom-audited in `CheckAxioms.lean`; the workflow also rejects unsolved placeholders and executes finite regressions.

## Proof organization and audited interfaces

1. **Genuine fibre rigidity:** `taylor_eppa_intrinsic_fibres` follows from the actual EPPA true-twin quotient contradiction and the intrinsic distance-three characterization, under a distinct even triple (merged before this checkpoint, #342). A two-graph with no distinct even triple instead has *every* distinct triple and is automatically homogeneous; the case split eliminates the even-triple hypothesis from the final theorem (#348).
2. **Exact induced group and 2-transitivity:** `taylor_eppa_two_graph_exact_and_two_transitive` uses explicit full XOR switching lifts and the EPPA-induced orbit argument, not Gardiner or rank-three classification (#343).
3. **Actual separating EPPA transversals:** `taylor_separating_eppa_transversal` constructs host automorphisms and correct EPPA embeddings, not just abstract side functions (#344).
4. **One-point extension, equal and complementary types:** the equal-type case extends a literal graph transposition by EPPA (#345). In the complementary case, separation permits a switched transversal on which the types agree. Crucially the image copy must be **reindexed along the induced fibre permutation**: it is an EPPA copy of `G.comap σ.symm`, not generally of the originally labelled `G` (#346).
5. **Finite-domain induction:** `two_graph_homogeneous_of_one_point_extensions` extends the restriction of a partial permutation to `R`, conjugates the remaining point to a map `a → b` fixing `R`, and composes the certified one-point extension; no assumption of coherent EPPA choices (#347).
6. **All-transversal consequence:** `odd_triple_transversal_iff` and `partial_transversal_preserves_two_graph` certify that switching leaves triple parity unchanged (#349). Lifting a full two-graph automorphism to the Taylor double need not preserve the sides of a given transversal. `taylor_lift_choice_agreement_uniform` shows the side discrepancy is constant across the finite partial-map domain, using actual pair adjacency; one global deck swap then completes the extension, including the empty-domain case (#350).

All proof PRs #343–#350 were merged into `main` after successful Lean builds and permitted-axiom audits.

## Remaining boundaries — do not overmark

- The **separate earlier lemma** `lemma:gtg` (partial two-graph automorphism and invariant switched representative) is **not** yet a complete standalone Lean theorem. Its arbitrary-size parity potential is verified, and a self-contained paper proof with finite checks is in `validation/section5-partial-twograph-selfcontained-proof.tex` and `validation/section5-partial-twograph-audit-20261019.md`. The remaining formalization is the directed-path and even/odd-cycle compatibility argument. The full-domain XOR lift needed by Proposition 5.11 **is** already independently proved in Lean.
- The new Lean proof certifies **Proposition 5.11's statements**, not the original paragraphs of `lem:second-transversal`, `lem:separation` and `prop:one-for-all` verbatim. Any later source marker should distinguish `theorem verified via alternative proof` from `printed proof verified line-by-line`.
- The previously identified low-order issue in the **introductory equivalence theorem** requiring a non-homogeneous transversal at `|X| ≤ 2` remains a separate manuscript question; it is not repaired by the all-orders homogeneous-two-graph theorem.
- Gardiner and rank-three graph classifications remain external inputs elsewhere in the manuscript, not ingredients of this proof.
- The separate Section 6 Sofia-review packet [PR #308](https://github.com/janhubicka/EPPA-III/pull/308) stays unmerged and unsent pending author review.

**Suggested next proof target:** finish `lemma:gtg` itself using the existing anchor discrepancy potential and the path/cycle argument from the standalone audit. Until then, do not mark that earlier lemma as Lean-verified.
