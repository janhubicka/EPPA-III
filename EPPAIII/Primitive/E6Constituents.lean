import EPPAIII.Primitive.NonlocalConnectivity
import EPPAIII.Primitive.SparseConstituent
import EPPAIII.Primitive.SmallConstituentGraphScreen
import Mathlib.Tactic.Ring

/-! # The E₆ shadow geometry exclusion from its published constituent data -/

namespace EPPAIII.Primitive

open SimpleGraph

private def eSixLocalOrder (q : ℕ) := q * (q ^ 3 + 1) * (q + 1) * (q ^ 2 + 1) * (q ^ 4 + 1)
private def eSixLocalDegree (q : ℕ) :=
  q ^ 2 * (q ^ 2 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) + q - 1
private def eSixNonlocalOrder (q : ℕ) := q ^ 8 * (q ^ 4 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)
private def eSixNonadjacentCommon (q : ℕ) := q ^ 6 + q ^ 5 + q ^ 4 + 2 * q ^ 3 + q ^ 2 + q + 1

/-- The strongly regular parameters of the collinearity graph of E₆,₁(q), in its
collinearity orientation. Their geometric identification is an input. -/
def eSixParameters (q : ℕ) : SRGParameters where
  order := eSixLocalOrder q + eSixNonlocalOrder q + 1
  degree := eSixLocalOrder q
  adjacentCommon := eSixLocalDegree q
  nonadjacentCommon := eSixNonadjacentCommon q

private theorem eSix_nonlocal_degree_gt_one {q : ℕ} (hq : 2 ≤ q) :
    1 < eSixLocalOrder q - eSixNonadjacentCommon q := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hq
  let degree := (t + 3) ^ 2 * ((2 + t) ^ 2 + 1) * (t ^ 2 + 3 * t + 3) ^ 2 *
    (t ^ 3 + 7 * t ^ 2 + 16 * t + 11)
  have hEq : eSixLocalOrder (2 + t) = eSixNonadjacentCommon (2 + t) + degree := by
    unfold eSixLocalOrder eSixNonadjacentCommon degree
    ring
  have hPos : 1 < degree := by
    have hSquare : 9 ≤ (t + 3) ^ 2 :=
      Nat.pow_le_pow_left (show 3 ≤ t + 3 by omega) 2
    have hFactors : 1 ≤ ((2 + t) ^ 2 + 1) * (t ^ 2 + 3 * t + 3) ^ 2 *
        (t ^ 3 + 7 * t ^ 2 + 16 * t + 11) := by
      have hSquare₂ : 9 ≤ (t ^ 2 + 3 * t + 3) ^ 2 :=
        Nat.pow_le_pow_left (show 3 ≤ t ^ 2 + 3 * t + 3 by omega) 2
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have hLower : (t + 3) ^ 2 ≤ degree := by
      simpa only [degree, Nat.mul_one, ← Nat.mul_assoc] using
        Nat.mul_le_mul_left ((t + 3) ^ 2) hFactors
    omega
  rw [hEq, Nat.add_sub_cancel_left]
  exact hPos

private theorem eSixLocal_degree_gt_one {q : ℕ} (hq : 2 ≤ q) : 1 < eSixLocalDegree q := by
  have h : 0 < q ^ 2 * (q ^ 2 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) := by
    have hq' : 0 < q := by omega
    exact Nat.mul_pos (Nat.mul_pos (pow_pos hq' _) (by omega)) (by omega)
  unfold eSixLocalDegree
  omega

private theorem eSixLocal_four_mul_degree_lt_order {q : ℕ} (hq : 2 ≤ q) :
    4 * eSixLocalDegree q < eSixLocalOrder q := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hq
  unfold eSixLocalDegree eSixLocalOrder
  let base := (2 + t) ^ 2 * ((2 + t) ^ 2 + 1) *
    ((2 + t) ^ 4 + (2 + t) ^ 3 + (2 + t) ^ 2 + (2 + t) + 1)
  change 4 * (base + (2 + t) - 1) < _
  rw [show base + (2 + t) - 1 = base + t + 1 by omega]
  let excess := (t + 3) * (t ^ 2 + 3 * t + 3) * (t ^ 3 + 7 * t ^ 2 + 17 * t + 13) *
    (t ^ 5 + 10 * t ^ 4 + 40 * t ^ 3 + 78 * t ^ 2 + 71 * t + 18)
  have hEq : (2 + t) * ((2 + t) ^ 3 + 1) * (2 + t + 1) *
      ((2 + t) ^ 2 + 1) * ((2 + t) ^ 4 + 1) = 4 * (base + t + 1) + excess := by
    unfold base excess
    ring
  have hPos : 0 < excess := by
    unfold excess
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
  omega

private theorem eSixNonlocal_four_mul_degree_lt_order {q : ℕ} (hq : 2 ≤ q) :
    4 * eSixLocalOrder q < eSixNonlocalOrder q := by
  have hPos : 0 < q := by omega
  have hPowerTwo := pow_pos hPos 2
  have hPowerThree := pow_pos hPos 3
  have hPowerSeven := pow_pos hPos 7
  unfold eSixLocalOrder eSixNonlocalOrder
  calc
    4 * (q * (q ^ 3 + 1) * (q + 1) * (q ^ 2 + 1) * (q ^ 4 + 1)) ≤
        4 * (q * (2 * q ^ 3) * (2 * q) * (2 * q ^ 2) * (q ^ 4 + 1)) := by
      exact Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right _ (Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.mul_le_mul_left q (by omega)) (by omega)) (by omega)))
    _ = 32 * (q ^ 7 * (q ^ 4 + 1)) := by ring
    _ < (q * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1)) * (q ^ 7 * (q ^ 4 + 1)) := by
      apply Nat.mul_lt_mul_of_pos_right _ (Nat.mul_pos hPowerSeven (by omega))
      have hPowerFive : 32 ≤ q ^ 5 := by exact Nat.pow_le_pow_left hq 5
      have hEq : q * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) = q ^ 5 + q ^ 4 + q ^ 3 + q ^ 2 + q := by
        ring
      omega
    _ = q ^ 8 * (q ^ 4 + 1) * (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) := by ring

/-- The second E₆ subconstituent is connected by the general strongly regular
connectivity criterion and the published host parameters. -/
theorem eSix_nonlocal_connected {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℕ} (hq : 2 ≤ q) (root : V)
    (hSRG : let p := eSixParameters q
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon) :
    (constituentGraph H root true).Connected := by
  change (nonlocalGraph H root).Connected
  refine nonlocalGraph_connected_of_degree_lt_order H hSRG ?_ root ?_
  · change 0 < q ^ 6 + q ^ 5 + q ^ 4 + 2 * q ^ 3 + q ^ 2 + q + 1
    omega
  · have hProfile := (constituentGraph_profile H (eSixParameters q) hSRG root true).1
    change Nat.card {x : V // root ≠ x ∧ ¬ H.Adj root x} =
      eSixLocalOrder q + eSixNonlocalOrder q + 1 - eSixLocalOrder q - 1 at hProfile
    rw [hProfile]
    change eSixLocalOrder q <
      eSixLocalOrder q + eSixNonlocalOrder q + 1 - eSixLocalOrder q - 1
    have hBound := eSixNonlocal_four_mul_degree_lt_order hq
    omega

/-- The E₆ constituent profiles follow from the published parameters.
The local graph is connected from its published clique-extension model.
Both actual constituents are excluded by sparsity. -/
theorem eSix_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {q : ℕ} (hq : 2 ≤ q) (root : V)
    (hSRG : let p := eSixParameters q
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hLocalConnected : (constituentGraph H root false).Connected) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  have hConnected (side : Bool) : (constituentGraph H root side).Connected := by
    cases side
    · exact hLocalConnected
    · exact eSix_nonlocal_connected H hq root hSRG
  have exclude (side : Bool) (n degree : ℕ)
      (hProfile : HasRegularProfile (constituentGraph H root side) (n, degree))
      (hPos : 1 < degree) (hQuarter : 4 * degree < n) := by
    let G := constituentGraph H root side
    have hRegular : G.IsRegularOfDegree degree := by
      intro x
      rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      exact hProfile.2 x
    have hOrder : Fintype.card (constituentSet H root side) = n :=
      Nat.card_eq_fintype_card.symm.trans hProfile.1
    exact sparseConnected_excludes_cliqueUnion_or_cover G (hConnected side) hRegular hPos
      (hOrder.symm ▸ hQuarter)
  cases side
  · exact exclude false _ _ (constituentGraph_profile H (eSixParameters q) hSRG root false)
      (eSixLocal_degree_gt_one hq)
      (eSixLocal_four_mul_degree_lt_order hq)
  · have hProfile := constituentGraph_profile H (eSixParameters q) hSRG root true
    have hOrder : ((eSixParameters q).constituentProfile true).1 = eSixNonlocalOrder q := by
      change eSixLocalOrder q + eSixNonlocalOrder q + 1 - eSixLocalOrder q - 1 = _
      omega
    exact exclude true _ _ ⟨hProfile.1.trans hOrder, hProfile.2⟩
      (eSix_nonlocal_degree_gt_one hq)
      ((Nat.mul_le_mul_left 4 (Nat.sub_le _ _)).trans_lt (eSixNonlocal_four_mul_degree_lt_order hq))

end EPPAIII.Primitive
