import EPPAIII.Primitive.NonlocalConnectivity
import EPPAIII.Primitive.SmallConstituentGraphScreen
import EPPAIII.Primitive.SparseConstituent
import Mathlib.Tactic.Ring

/-! # Second constituents of rank-two polar graphs -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- The order and degree of the nonlocal polar graph, with the four
threshold regimes occurring in rank two over fields of order at least three.
The split rook case is treated independently. -/
def RankTwoPolarRange (Q t : ℕ) : Prop :=
  (4 ≤ Q ∧ 4 ≤ t) ∨ (5 ≤ Q ∧ 3 ≤ t) ∨ (Q = 3 ∧ 9 ≤ t) ∨ (Q = 3 ∧ t = 3)

private theorem polar_rankTwo_sparse_large {Q t : ℕ}
    (h : (4 ≤ Q ∧ 4 ≤ t) ∨ (5 ≤ Q ∧ 3 ≤ t) ∨ (Q = 3 ∧ 9 ≤ t)) :
    4 * ((Q - 1) * (t + 1)) < Q ^ 2 * t := by
  rcases h with ⟨hQ, ht⟩ | ⟨hQ, ht⟩ | ⟨rfl, ht⟩
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hQ
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show (4 + a - 1 : ℕ) = 3 + a by omega]
    have hOrder : (4 + a) ^ 2 * (4 + b) =
        4 * ((3 + a) * (4 + b + 1)) + (4 * a ^ 2 + 12 * a + (a + 2) ^ 2 * b) + 4 := by
      ring
    omega
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hQ
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show (5 + a - 1 : ℕ) = 4 + a by omega]
    have hOrder : (5 + a) ^ 2 * (3 + b) =
        4 * ((4 + a) * (3 + b + 1)) + (3 * a ^ 2 + 14 * a + (a + 3) ^ 2 * b) + 11 := by
      ring
    omega
  · simp only [Nat.reducePow, Nat.reduceSub]
    omega

/-- For the rank-two polar parameters, the nonlocal graph has none of the
four model forms allowed for a half-order constituent in Section 8. -/
theorem polar_rankTwo_second_constituent_excludes_forms {U : Type*} [Fintype U]
    (J : SimpleGraph U) [DecidableRel J.Adj] {Q t : ℕ} (hRange : RankTwoPolarRange Q t)
    (hOrder : Fintype.card U = Q ^ 2 * t)
    (hRegular : J.IsRegularOfDegree ((Q - 1) * (t + 1))) (hConnected : J.Connected) :
    (∀ s b, IsEmpty (J ≃g cliqueUnion s b)) ∧
    (∀ s b, IsEmpty (J ≃g (cliqueUnion s b)ᶜ)) ∧
    (∀ s b X Y, IsEmpty (J ≃g coverGraph s b X Y)) ∧
    (∀ s b X Y, IsEmpty (J ≃g (coverGraph s b X Y)ᶜ)) := by
  have hCases : ((4 ≤ Q ∧ 4 ≤ t) ∨ (5 ≤ Q ∧ 3 ≤ t) ∨ (Q = 3 ∧ 9 ≤ t)) ∨
      (Q = 3 ∧ t = 3) := by
    simpa only [RankTwoPolarRange, or_assoc] using hRange
  rcases hCases with hLarge | ⟨rfl, rfl⟩
  · have hQ : 3 ≤ Q := by rcases hLarge with ⟨hQ, _⟩ | ⟨hQ, _⟩ | ⟨hQ, _⟩ <;> omega
    have hDegree : 1 < (Q - 1) * (t + 1) := by
      exact (by omega : 1 < Q - 1).trans_le
        (Nat.le_mul_of_pos_right _ (show 0 < t + 1 from Nat.succ_pos t))
    exact sparseConnected_excludes_cliqueUnion_or_cover J hConnected hRegular hDegree
      (by rw [hOrder]; exact polar_rankTwo_sparse_large hLarge)
  · have hSparse : 2 * 8 + 2 < Fintype.card U := by rw [hOrder]; decide
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s b
      exact ⟨fun φ => sparseConnected_not_cliqueUnion_or_compl J hConnected hRegular
        (by decide) hSparse (Or.inl ⟨φ⟩)⟩
    · intro s b
      exact ⟨fun φ => sparseConnected_not_cliqueUnion_or_compl J hConnected hRegular
        (by decide) hSparse (Or.inr ⟨φ⟩)⟩
    · intro s b X Y
      refine ⟨fun φ => ?_⟩
      have hEven := order_even_of_cover_or_compl J X Y (Or.inl ⟨φ⟩)
      rw [hOrder] at hEven
      exact (by decide : ¬ ((3 ^ 2 * 3 : ℕ) % 2 = 0)) hEven
    · intro s b X Y
      refine ⟨fun φ => ?_⟩
      have hEven := order_even_of_cover_or_compl J X Y (Or.inr ⟨φ⟩)
      rw [hOrder] at hEven
      exact (by decide : ¬ ((3 ^ 2 * 3 : ℕ) % 2 = 0)) hEven

/-- The rank-two polar SRG data, with (Q+1) points per line and (t+1)
lines at each point. -/
def rankTwoPolarParameters (Q t : ℕ) : SRGParameters :=
  ⟨(Q + 1) * (Q * t + 1), Q * (t + 1), Q - 1, t + 1⟩

/-- The actual nonlocal graph satisfies the rank-two polar exclusion. The
published SRG tuple already forces the needed connectivity. -/
theorem polar_rankTwo_actual_second_constituent_excludes_forms {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {Q t : ℕ} (hRange : RankTwoPolarRange Q t)
    (h : H.IsSRGWith ((Q + 1) * (Q * t + 1)) (Q * (t + 1)) (Q - 1) (t + 1))
    (root : V) :
    (∀ s b, IsEmpty (nonlocalGraph H root ≃g cliqueUnion s b)) ∧
    (∀ s b, IsEmpty (nonlocalGraph H root ≃g (cliqueUnion s b)ᶜ)) ∧
    (∀ s b X Y, IsEmpty (nonlocalGraph H root ≃g coverGraph s b X Y)) ∧
    (∀ s b X Y, IsEmpty (nonlocalGraph H root ≃g (coverGraph s b X Y)ᶜ)) := by
  classical
  let J := nonlocalGraph H root
  have hQ : 3 ≤ Q := by
    rcases hRange with ⟨hQ, _⟩ | ⟨hQ, _⟩ | ⟨hQ, _⟩ | ⟨hQ, _⟩ <;> omega
  have ht : 3 ≤ t := by
    rcases hRange with ⟨_, ht⟩ | ⟨_, ht⟩ | ⟨_, ht⟩ | ⟨_, ht⟩ <;> omega
  have hProfile := constituentGraph_profile H (rankTwoPolarParameters Q t) h root true
  have hOrder : Fintype.card {x : V // root ≠ x ∧ ¬ H.Adj root x} = Q ^ 2 * t := by
    have hCard := hProfile.1
    change Nat.card {x : V // root ≠ x ∧ ¬ H.Adj root x} =
      (Q + 1) * (Q * t + 1) - Q * (t + 1) - 1 at hCard
    rw [Nat.card_eq_fintype_card] at hCard
    have hIdentity : (Q + 1) * (Q * t + 1) = Q ^ 2 * t + Q * (t + 1) + 1 := by ring
    omega
  have hRegular : J.IsRegularOfDegree ((Q - 1) * (t + 1)) := by
    intro x
    rw [← J.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    have hDegree := hProfile.2 x
    change Nat.card (J.neighborSet x) = Q * (t + 1) - (t + 1) at hDegree
    have hIdentity : Q * (t + 1) = (Q - 1) * (t + 1) + (t + 1) := by
      calc
        Q * (t + 1) = ((Q - 1) + 1) * (t + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = _ := by rw [Nat.add_mul, Nat.one_mul]
    omega
  have hConnected : J.Connected := by
    apply nonlocalGraph_connected_of_degree_lt_order H h (by omega) root
    rw [Nat.card_eq_fintype_card, hOrder, pow_two, Nat.mul_assoc]
    apply Nat.mul_lt_mul_of_pos_left _ (by omega)
    have hBound := Nat.mul_le_mul_right t (show 2 ≤ Q by omega)
    omega
  exact polar_rankTwo_second_constituent_excludes_forms J hRange hOrder hRegular hConnected

end EPPAIII.Primitive
