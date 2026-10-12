import Mathlib

/-!
# Equal edge counts determine the degree of finite regular graphs

The handshaking lemma gives |V| * d = 2 * |E| for a d-regular
finite graph. Hence two regular graphs on the same nonempty vertex
set with equal edge counts have the same degree.

This lemma will distinguish the four natural S_t wr S_s-invariant
graph patterns in the one-partial-coordinate case of Lemma 3.7
without enumerating their edge sets or manipulating binomial formulas.
-/

namespace EPPAIII.CliqueCovers

/-- Two regular graphs on one nonempty finite vertex type with
the same number of edges have the same regular degree. -/
theorem equal_degree_of_regular_equal_edges
    {V : Type*} [Fintype V]
    (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (dG dH : ℕ)
    (hPos : 0 < Fintype.card V)
    (hG : G.IsRegularOfDegree dG)
    (hH : H.IsRegularOfDegree dH)
    (hEdges : G.edgeFinset.card = H.edgeFinset.card) :
    dG = dH := by
  classical
  have hSumG :
      (∑ v : V, G.degree v) = Fintype.card V * dG := by
    calc
      (∑ v : V, G.degree v) = ∑ _v : V, dG := by
        apply Finset.sum_congr rfl
        intro v _
        exact hG v
      _ = Fintype.card V * dG := by simp
  have hSumH :
      (∑ v : V, H.degree v) = Fintype.card V * dH := by
    calc
      (∑ v : V, H.degree v) = ∑ _v : V, dH := by
        apply Finset.sum_congr rfl
        intro v _
        exact hH v
      _ = Fintype.card V * dH := by simp
  have hMul : Fintype.card V * dG = Fintype.card V * dH := by
    calc
      Fintype.card V * dG = ∑ v : V, G.degree v := hSumG.symm
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
      _ = 2 * H.edgeFinset.card := by rw [hEdges]
      _ = ∑ v : V, H.degree v := (H.sum_degrees_eq_twice_card_edges).symm
      _ = Fintype.card V * dH := hSumH
  exact Nat.eq_of_mul_eq_mul_left hPos hMul

end EPPAIII.CliqueCovers
