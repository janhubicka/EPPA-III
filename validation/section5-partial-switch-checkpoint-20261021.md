# Section 5.1 partial two-graph switching — validation checkpoint, 21 October 2026

**Source:** frozen `main-new(20261019-085906).tex`, label `lemma:gtg`. The standalone suggested paper proof is `validation/section5-partial-twograph-selfcontained-proof.tex`; the October 19 adversarial audit is `validation/section5-partial-twograph-audit-20261019.md`. Nothing here modifies the author manuscript or sends comments to Sofia.

## Formalized pieces

| Mathematical step | Axiom-audited Lean declarations | PR |
|---|---|---|
| Partial maps having a fixed vertex | `anchored_transversal_adj_iff_odd`, `partial_two_graph_fixed_point_switch` | #352 — merged, green |
| Generic pair discrepancy telescoping, including swapped endpoints | `pair_discrepancy_telescopes`, `pair_cycle_xor_sums_equal`, `pair_swapped_cycle_xor_sums_equal` | #353 — merged, green |
| Partial two-graph parity implies a Boolean vertex potential | `partial_two_graph_discrepancy_potential` | #354 — merged, green |
| Vertex equations suffice for actual graph switching | `partial_switch_of_vertex_equations` | #354 — merged, green |
| Open directed paths by finite source elimination | `vertex_equations_of_partial_sources`, `partial_two_graph_acyclic_switch` | #355 — merged, green |
| Even periodic orbit has zero sum of vertex potential | `xorPrefix_add`, `partial_pair_trajectories_cycle_sums_equal`, `partial_even_cycle_potential_zero` | #356 — merged, green |
| Two odd cyclic orbits have the same vertex-potential sum | `xorPrefix_repeated_blocks`, `xorPrefix_odd_constant`, `partial_odd_cycles_potential_equal_of_returns` | #357 — CI pending for strengthened return-only form |

The merged declarations are registered in `CheckAxioms.lean`, and each PR underwent the full Lean build, permitted-axiom audit, finite regressions and placeholder-rejection workflow. The #357 status must be updated only after its final build succeeds.

## Exact remaining theorem

For a finite vertex set `V`, graph `G`, finite domain `D` and permutation `p : Equiv.Perm V` whose restriction to `D` preserves odd triple parity, prove

```lean
∃ t : V → Bool,
  IsPartialGraphAutomorphism (taylorTransversalGraph G t) D p
```

The verified `partial_two_graph_discrepancy_potential` supplies a global Boolean function `h` satisfying, for all `x,y ∈ D`,

```text
edge(x,y) XOR edge(p x,p y) = h(x) XOR h(y).
```

The verified switching bridge reduces the target to finding **one** Boolean `c` and a function `t` with

```text
t(x) XOR t(p x) = h(x) XOR c,  x ∈ D.
```

The **mathematical compatibility conditions** for the finite functional graph of `p|D` are now isolated:
- Every even cycle has zero XOR-sum of `h` (theorem #356).
- The XOR-sums of any two odd cycles agree (theorem #357, pending final integration).
- Paths have no compatibility condition, and finite source elimination solves their equations (theorem #355).

## Still required for a complete formal proof of `lemma:gtg`

1. **Finite orbit structure:** extract from `p|D` disjoint open directed paths and closed directed cycles, or prove an equivalent elimination lemma. Use only ordinary finiteness/injectivity, and avoid extra hypotheses on `G`.
2. **One global bit:** take `c` equal to the common odd-cycle potential sum if some odd cycle exists, and `false` otherwise. Formally connect #356/#357 to the cycle equations `sum_C h = (|C| mod 2) * c`.
3. **Cycle propagation and glue:** choose a side bit at one vertex of each cycle, propagate around it, and use the matching cycle sum for consistency. Combine with the existing source-elimination theorem for paths, without changing previously solved equations.
4. **Final assembly:** pass the solution to `partial_switch_of_vertex_equations`, and export an axiom-audited theorem with **exactly** the original partial-two-graph hypotheses.

Do **not** mark `lemma:gtg` fully Lean-verified before these four interfaces are certified. Proposition 5.11's separate homogeneity and all-switching-transversal conclusions were verified independently in PRs #347–#350 and do not close this earlier lemma.

## Paper-level audit

The earlier manuscript's inductive path argument implicitly uses a previously chosen pair when processing the first nonperiodic path. The self-contained alternative proof avoids that order-of-construction problem and directly treats the discrepancy potential, even cycles, odd cycles and all open paths. Its correctness is supported by independent finite certificates, but it is not the formal Lean theorem until the preceding gluing steps are complete. The manuscript remains frozen until Sofia's review.
