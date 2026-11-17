import EPPAIII.Primitive.CliqueProfileDivisibility
import EPPAIII.Primitive.PolarRankTwoExclusion
import EPPAIII.Primitive.UnitaryFiveTwoArithmetic

/-! # The two small elliptic point graph exclusions -/

namespace EPPAIII.Primitive

open SimpleGraph
open scoped BigOperators

private theorem multiplicity_le_six {Q d : ℕ} (m : Fin Q → ℕ) (hSeven : ¬ 7 ∣ d)
    (hDiv : (∏ j, (j.val + 1).factorial ^ m j * (m j).factorial) ∣ d)
    (j : Fin Q) : m j ≤ 6 := by
  by_contra! hLarge
  have hFactorial : 7 ∣ (m j).factorial := Nat.dvd_factorial (by decide) (by omega)
  have hFactor : 7 ∣ (j.val + 1).factorial ^ m j * (m j).factorial :=
    hFactorial.trans (dvd_mul_left _ _)
  exact hSeven (hFactor.trans ((Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans hDiv))

private theorem fin3_succ_zero : (0 : Fin 2).succ = (1 : Fin 3) := rfl
private theorem fin3_succ_succ_zero : (0 : Fin 1).succ.succ = (2 : Fin 3) := rfl
private theorem fin4_succ_zero : (0 : Fin 3).succ = (1 : Fin 4) := rfl
private theorem fin4_succ_succ_zero : (0 : Fin 2).succ.succ = (2 : Fin 4) := rfl
private theorem fin4_succ_succ_succ_zero : (0 : Fin 1).succ.succ.succ = (3 : Fin 4) := rfl

set_option maxRecDepth 50000 in
private theorem ellipticThree_profile_check :
    ∀ a b c : Fin 7, 15 ≤ a.val + 2 * b.val + 3 * c.val →
      ¬ (fourCliqueSizesAutOrder a.val b.val c.val 0 ∣ 233280) := by
  decide

set_option maxRecDepth 50000 in
private theorem ellipticFour_profile_check :
    ∀ a b c d : Fin 7, 34 ≤ a.val + 2 * b.val + 3 * c.val + 4 * d.val →
      ¬ (fourCliqueSizesAutOrder a.val b.val c.val d.val ∣ 12533760) := by
  decide

private theorem ellipticThree_profile_false (m : Fin 3 → ℕ)
    (hSize : 15 ≤ ∑ j, m j * (j.val + 1))
    (hDiv : (∏ j, (j.val + 1).factorial ^ m j * (m j).factorial) ∣ 233280) :
    False := by
  let m' (j : Fin 3) : Fin 7 := ⟨m j, Nat.lt_succ_of_le (multiplicity_le_six m (by decide) hDiv j)⟩
  apply ellipticThree_profile_check (m' 0) (m' 1) (m' 2)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      fin3_succ_zero, fin3_succ_succ_zero] at hSize
    change 15 ≤ m 0 + 2 * m 1 + 3 * m 2
    norm_num [mul_comm, add_assoc] at hSize ⊢
    exact hSize
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero,
      fin3_succ_zero, fin3_succ_succ_zero, mul_one] at hDiv
    change fourCliqueSizesAutOrder (m 0) (m 1) (m 2) 0 ∣ 233280
    norm_num [fourCliqueSizesAutOrder, Nat.factorial, mul_assoc] at hDiv ⊢
    exact hDiv

private theorem ellipticFour_profile_false (m : Fin 4 → ℕ)
    (hSize : 34 ≤ ∑ j, m j * (j.val + 1))
    (hDiv : (∏ j, (j.val + 1).factorial ^ m j * (m j).factorial) ∣ 12533760) :
    False := by
  let m' (j : Fin 4) : Fin 7 := ⟨m j, Nat.lt_succ_of_le (multiplicity_le_six m (by decide) hDiv j)⟩
  apply ellipticFour_profile_check (m' 0) (m' 1) (m' 2) (m' 3)
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      fin4_succ_zero, fin4_succ_succ_zero, fin4_succ_succ_succ_zero] at hSize
    change 34 ≤ m 0 + 2 * m 1 + 3 * m 2 + 4 * m 3
    norm_num [mul_comm, add_assoc] at hSize ⊢
    exact hSize
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero,
      fin4_succ_zero, fin4_succ_succ_zero, fin4_succ_succ_succ_zero, mul_one] at hDiv
    change fourCliqueSizesAutOrder (m 0) (m 1) (m 2) (m 3) ∣ 12533760
    norm_num [fourCliqueSizesAutOrder, Nat.factorial, mul_assoc] at hDiv ⊢
    exact hDiv

/-- The elliptic rank-two point graph over 𝔽₃ has no half-order EPPA
selection subject to the constituent shape implication. -/
theorem ellipticSixThree_not_eppa
    {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (root : V) (hSRG : H.IsSRGWith 112 30 2 10)
    (φ : localGraph H (e root) ≃g cliqueUnion 10 3)
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root)))
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) ∣ 233280) : False := by
  have hRange : RankTwoPolarRange 3 9 := Or.inr (Or.inr (Or.inl ⟨by decide, by decide⟩))
  have hLocalHalf := selected_local_at_least_half_of_rankTwoPolar G H e hHalf hTrans root
    hRange hSRG hShape
  have hOrder : Nat.card (H.neighborSet (e root)) = 30 := by
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr φ.toEquiv
  obtain ⟨m, _, hWeight, hDiv⟩ := local_cliqueProfile_order_dvd_root_stabilizer G H e heppa root φ
  exact ellipticThree_profile_false m (by omega) (hDiv.trans hStabilizer)

/-- The elliptic rank-two point graph over 𝔽₄ has no half-order EPPA
selection subject to the constituent shape implication. -/
theorem ellipticSixFour_not_eppa
    {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (root : V) (hSRG : H.IsSRGWith 325 68 3 17)
    (φ : localGraph H (e root) ≃g cliqueUnion 17 4)
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root)))
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) ∣ 12533760) : False := by
  have hRange : RankTwoPolarRange 4 16 := Or.inl ⟨by decide, by decide⟩
  have hLocalHalf := selected_local_at_least_half_of_rankTwoPolar G H e hHalf hTrans root
    hRange hSRG hShape
  have hOrder : Nat.card (H.neighborSet (e root)) = 68 := by
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr φ.toEquiv
  obtain ⟨m, _, hWeight, hDiv⟩ := local_cliqueProfile_order_dvd_root_stabilizer G H e heppa root φ
  exact ellipticFour_profile_false m (by omega) (hDiv.trans hStabilizer)

end EPPAIII.Primitive
