import EPPAIII.Primitive.CliqueProfileDivisibility
import EPPAIII.Primitive.PolarRankTwoExclusion
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.NormNum

/-! # The two rank-three quadrangles of order (5,5) -/

namespace EPPAIII.Primitive

open scoped BigOperators

private def symplecticFiveCliqueOrders (a b c d e : ℕ) : ℕ :=
  a.factorial * (2 ^ b * b.factorial) * (6 ^ c * c.factorial) *
    (24 ^ d * d.factorial) * (120 ^ e * e.factorial)

private theorem symplecticFiveProfileFinite : ∀ a b c d e : Fin 7,
    a.val + b.val + c.val + d.val + e.val ≤ 6 →
    15 ≤ a.val + 2 * b.val + 3 * c.val + 4 * d.val + 5 * e.val →
    ¬ symplecticFiveCliqueOrders a.val b.val c.val d.val e.val ∣ 60000 := by
  decide +kernel

/-- Fifteen or more selected vertices in six cliques of width five force an
inadmissible divisor of the published full root-stabilizer order. -/
theorem symplecticFive_profile_order_not_dvd (m : Fin 5 → ℕ)
    (hSlots : (∑ j, m j) ≤ 6) (hVertices : 15 ≤ ∑ j, m j * (j.val + 1)) :
    ¬ (∏ j : Fin 5, (j.val + 1).factorial ^ m j * (m j).factorial) ∣ 60000 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hSlots hVertices
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.reduceAdd, Nat.factorial, pow_zero,
    one_pow, mul_one, one_mul] at hVertices ⊢
  let a := m 0
  let b := m (0 : Fin 4).succ
  let c := m (0 : Fin 3).succ.succ
  let d := m (0 : Fin 2).succ.succ.succ
  let e := m (0 : Fin 1).succ.succ.succ.succ
  change a + (b + (c + (d + e))) ≤ 6 at hSlots
  have hCount : 15 ≤ a + 2 * b + 3 * c + 4 * d + 5 * e := by
    change 15 ≤ a + (b * 2 + (c * 3 + (d * 4 + e * 5))) at hVertices
    omega
  have h := symplecticFiveProfileFinite ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩
    ⟨d, by omega⟩ ⟨e, by omega⟩ (by change a + b + c + d + e ≤ 6; omega) hCount
  change ¬ symplecticFiveCliqueOrders a b c d e ∣ 60000 at h
  simpa only [symplecticFiveCliqueOrders, show Nat.succ 0 = 1 from rfl, one_pow, one_mul, mul_assoc] using h

/-- The two 156-vertex quadrangles are excluded using their local six
cliques of size five and the order of their full root stabilizer. -/
theorem symplecticFourFive_not_eppa
    {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (root : V) (hSRG : H.IsSRGWith 156 30 4 6)
    (hLocalModel : localGraph H (e root) ≃g cliqueUnion 6 5)
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root)))
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) = 60000) : False := by
  have hRange : RankTwoPolarRange 5 5 := Or.inl ⟨by decide, by decide⟩
  have hLocalHalf := selected_local_at_least_half_of_rankTwoPolar G H e hHalf hTrans root
    hRange hSRG hShape
  have hOrder : Nat.card (H.neighborSet (e root)) = 30 := by
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr hLocalModel.toEquiv
  obtain ⟨m, hSlots, hCount, hDiv⟩ :=
    local_cliqueProfile_order_dvd_root_stabilizer G H e heppa root hLocalModel
  rw [hStabilizer] at hDiv
  exact symplecticFive_profile_order_not_dvd m hSlots (by omega) hDiv

end EPPAIII.Primitive
