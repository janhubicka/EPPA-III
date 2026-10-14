import EPPAIII.CliqueCovers.Basic

/-!
# Symmetric bipartite double-counting

For finite sets S,T in a simple graph, count the edges between
them twice, once from S and once from T. If every u in S has
exactly r neighbours in T and every v in T has exactly r
neighbours in S, where r>0, then S and T have the same size.

This elementary statement is the final cancellation in the
Case-1 calculation k_i*r = (m-k_j)*r of Lemma 3.12.
It does not assume the required per-block regularity: that
comes from the separate EPPA action and mixed-edge lemmas.
-/

namespace EPPAIII.BlockSystems

/-- Count neighbours of a vertex in an arbitrary finite subset
as an indicator sum. -/
theorem neighbour_filter_card_as_sum {W : Type*}
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (u : W) (T : Finset W) :
    (∑ v ∈ T, if H.Adj u v then (1 : ℕ) else 0) =
      (T.filter (fun v => H.Adj u v)).card := by
  classical
  simp

/-- Two-sided regularity of the bipartite edge relation
forces equal cardinalities of the two parts when r>0.
The sets need not even be disjoint. -/
theorem symmetric_bipartite_regular_card_eq {W : Type*}
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (S T : Finset W) (r : ℕ) (hr : 0 < r)
    (hS : ∀ u ∈ S, (T.filter (fun v => H.Adj u v)).card = r)
    (hT : ∀ v ∈ T, (S.filter (fun u => H.Adj v u)).card = r) :
    S.card = T.card := by
  classical
  have hRow :
      (∑ u ∈ S, ∑ v ∈ T, if H.Adj u v then (1 : ℕ) else 0) =
        S.card * r := by
    calc
      (∑ u ∈ S, ∑ v ∈ T, if H.Adj u v then (1 : ℕ) else 0) =
          ∑ u ∈ S, r := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [neighbour_filter_card_as_sum H u T, hS u hu]
      _ = S.card * r := by simp
  have hCol :
      (∑ v ∈ T, ∑ u ∈ S, if H.Adj v u then (1 : ℕ) else 0) =
        T.card * r := by
    calc
      (∑ v ∈ T, ∑ u ∈ S, if H.Adj v u then (1 : ℕ) else 0) =
          ∑ v ∈ T, r := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [neighbour_filter_card_as_sum H v S, hT v hv]
      _ = T.card * r := by simp
  have hSwitch :
      (∑ u ∈ S, ∑ v ∈ T, if H.Adj u v then (1 : ℕ) else 0) =
        (∑ v ∈ T, ∑ u ∈ S, if H.Adj v u then (1 : ℕ) else 0) := by
    calc
      (∑ u ∈ S, ∑ v ∈ T, if H.Adj u v then (1 : ℕ) else 0) =
          ∑ v ∈ T, ∑ u ∈ S, if H.Adj u v then (1 : ℕ) else 0 :=
        Finset.sum_comm
      _ = (∑ v ∈ T, ∑ u ∈ S, if H.Adj v u then (1 : ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro u hu
        by_cases hadj : H.Adj u v
        · simp [hadj, hadj.symm]
        · have hn : ¬ H.Adj v u := fun h => hadj h.symm
          simp [hadj, hn]
  have hMul : S.card * r = T.card * r :=
    hRow.symm.trans (hSwitch.trans hCol)
  exact (mul_right_cancel₀ (Nat.ne_of_gt hr)) hMul

end EPPAIII.BlockSystems
