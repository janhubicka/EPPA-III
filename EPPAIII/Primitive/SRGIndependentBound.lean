import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Tactic.Ring

/-! # A common-neighbour bound on independent sets in strongly regular graphs -/

namespace EPPAIII.Primitive

open SimpleGraph
open scoped BigOperators

/-- Count neighbours of an independent set at every vertex, then apply
Cauchy–Schwarz to their first and second moments. -/
theorem srg_independent_size_bound {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {n k l μ m : ℕ} (h : H.IsSRGWith n k l μ)
    (f : Fin m ↪ V) (hf : ∀ i j, ¬ H.Adj (f i) (f j)) :
    (m * k) ^ 2 ≤ n * (m * k + m * (m - 1) * μ) := by
  classical
  let adj (i : Fin m) (v : V) : ℕ := if H.Adj (f i) v then 1 else 0
  let d (v : V) : ℕ := ∑ i, adj i v
  have first (i : Fin m) : ∑ v, adj i v = k := by
    have heq : (Finset.univ.filter fun v => H.Adj (f i) v) = H.neighborFinset (f i) := by
      ext v
      simp
    rw [show (∑ v, adj i v) = _ by exact Finset.sum_boole _ _, heq]
    exact h.regular (f i)
  have second (i j : Fin m) :
      ∑ v, adj i v * adj j v = if i = j then k else μ := by
    by_cases hEq : i = j
    · subst j
      rw [ite_eq_left rfl, ← first i]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : H.Adj (f i) v <;> simp [adj, hv]
    · rw [ite_eq_right hEq]
      have hSum :
          (∑ v, adj i v * adj j v) =
            ∑ v, if v ∈ H.commonNeighbors (f i) (f j) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hi : H.Adj (f i) v <;> by_cases hj : H.Adj (f j) v <;>
          simp [adj, H.mem_commonNeighbors, hi, hj]
      rw [hSum, Finset.sum_boole]
      have hCard : (Finset.univ.filter fun v => v ∈ H.commonNeighbors (f i) (f j)).card =
          Fintype.card (H.commonNeighbors (f i) (f j)) := by
        rw [Fintype.card_of_subtype]
        simp
      rw [hCard]
      exact h.of_not_adj (f.injective.ne hEq) (hf i j)
  have sumFirst : ∑ v, d v = m * k := by
    unfold d
    rw [Finset.sum_comm]
    simp [first]
  have sumSecond : ∑ v, d v ^ 2 = m * k + m * (m - 1) * μ := by
    calc
      ∑ v, d v ^ 2 = ∑ v, ∑ i, ∑ j, adj i v * adj j v := by
        apply Finset.sum_congr rfl
        intro v _
        change (∑ i, adj i v) ^ 2 = _
        rw [pow_two, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
      _ = ∑ i, ∑ j, ∑ v, adj i v * adj j v := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := by
        simp only [second]
        have hRow (i : Fin m) : (∑ j, if i = j then k else μ) = k + (m - 1) * μ := by
          have hi : i ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ _
          rw [← Finset.add_sum_erase _ _ hi, ite_eq_left rfl]
          rw [Finset.sum_congr rfl (fun j hj =>
            ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hj)))]
          simp
        simp only [hRow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        change m * (k + (m - 1) * μ) = _
        ring
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset V)) (f := d)
  rwa [Finset.card_univ, h.card, sumFirst, sumSecond] at hCS

end EPPAIII.Primitive
