import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

namespace EPPAIII.Primitive

/-- A strongly regular graph locally `T(4)` has order eight and nonedge parameter six.
The lower bound on that parameter counts four common local neighbours and the root. -/
theorem locallyTriangular_four_srg_order
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n μ : ℕ} (h : G.IsSRGWith n 6 4 μ) (hn : 0 < n) (hμ : 5 ≤ μ) :
    n = 8 ∧ μ = 6 := by
  have hparams : 6 = (n - 7) * μ := h.param_eq G hn
  have hdifference : n - 7 = 1 := by
    have hlarge : ¬ 2 ≤ n - 7 := by
      intro hle
      have hmul := Nat.mul_le_mul_right μ hle
      omega
    have hne : n - 7 ≠ 0 := by
      intro hz
      simp [hz] at hparams
    omega
  refine ⟨by omega, ?_⟩
  simpa [hdifference] using hparams.symm

/-- The strongly regular parameter identity rules out both exceptional orders in the
classification of connected locally Petersen graphs. The order list is an input. -/
theorem locallyComplementTriangular_five_srg_order
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n μ : ℕ} (h : G.IsSRGWith n 10 3 μ) (hn : n = 21 ∨ n = 63 ∨ n = 65) :
    n = 21 := by
  obtain rfl | rfl | rfl := hn
  · rfl
  · have hparams : 60 = 52 * μ := h.param_eq G (by decide)
    omega
  · have hparams : 60 = 54 * μ := h.param_eq G (by decide)
    omega

/-- The strongly regular parameter identity rules out order 32 in the classification of
connected locally `KG(6, 2)` graphs. The order list is an input. -/
theorem locallyComplementTriangular_six_srg_order
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n μ : ℕ} (h : G.IsSRGWith n 15 6 μ) (hn : n = 28 ∨ n = 32 ∨ n = 36) :
    n = 28 ∨ n = 36 := by
  obtain rfl | rfl | rfl := hn
  · exact Or.inl rfl
  · have hparams : 120 = 16 * μ := h.param_eq G (by decide)
    omega
  · exact Or.inr rfl

end EPPAIII.Primitive
