import EPPAIII.TwoGraphs.TrivialTwoGraph

/-!
# Both trivial two-graphs are homogeneous

The Section 5 converse invokes a theorem stated only for nontrivial
two-graphs. This file supplies the missing exact trivial-case interface:
the empty and complete two-graphs need no EPPA, fibre rigidity, or
Gardiner classification.

An empty two-graph means no odd-parity triple; a complete two-graph
means that no distinct triple has even parity. Both are preserved by
every vertex permutation, hence every partial permutation extends.
-/

namespace EPPAIII.TwoGraphs

/-- If every triple has even edge parity, every permutation is a
two-graph automorphism, and all finite partial permutations extend. -/
theorem no_odd_triple_two_graph_homogeneous
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNoOdd : ∀ x y z : V, ¬ OddBaseTriple G x y z) :
    IsHomogeneousTwoGraph G := by
  intro D p _
  refine ⟨p, ?_, ?_⟩
  · intro x y z
    constructor
    · intro hx
      exact False.elim (hNoOdd x y z hx)
    · intro hy
      exact False.elim (hNoOdd (p x) (p y) (p z) hy)
  · intro x _
    rfl

/-- No source-facing (2) -> (3) argument may invoke the nontrivial
fibre-rigidity theorem before disposing of these two elementary cases. -/
theorem trivial_two_graph_homogeneous
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTrivial :
      (∀ x y z : V, ¬ OddBaseTriple G x y z) ∨
      (¬ ∃ a b c : V,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ EvenTriple G a b c)) :
    IsHomogeneousTwoGraph G := by
  rcases hTrivial with hEmpty | hComplete
  · exact no_odd_triple_two_graph_homogeneous G hEmpty
  · exact no_even_triple_two_graph_homogeneous G hComplete

end EPPAIII.TwoGraphs
