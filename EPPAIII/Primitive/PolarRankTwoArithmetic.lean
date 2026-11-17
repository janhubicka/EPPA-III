import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # The large-field point-stabilizer estimates in polar rank two -/

namespace EPPAIII.Primitive

private theorem le_half_factorial {n : ℕ} (hn : 8 ≤ n) : n ≤ (n / 2).factorial := by
  let m := n / 2
  have hm : 4 ≤ m := by dsimp [m]; omega
  have hFact : m.factorial = m * (m - 1).factorial := by
    have hmStep : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    calc
      m.factorial = (m - 1 + 1).factorial := congrArg Nat.factorial hmStep.symm
      _ = _ := by rw [Nat.factorial_succ, hmStep]
  have hFactor : 3 ≤ (m - 1).factorial := (by omega : 3 ≤ m - 1).trans (Nat.self_le_factorial _)
  have hThree := Nat.mul_le_mul_left m hFactor
  rw [hFact]
  exact (by dsimp [m]; omega : n ≤ m * 3).trans hThree

/-- For every field order at least eight, the product-factorial lower bound
exceeds the respective published point-stabilizer order. The four formulas
are for symplectic (or odd orthogonal), elliptic orthogonal, even unitary,
and odd unitary rank-two polar graphs. -/
theorem polar_rankTwo_large_stabilizer_bounds (q f : ℕ) (hq : 8 ≤ q) (hf : f ≤ q) :
    f * q ^ 4 * (q - 1) * (q ^ 2 - 1) < (q / 2).factorial ^ (q + 1) ∧
    2 * f * q ^ 6 * (q - 1) * (q ^ 4 - 1) < (q / 2).factorial ^ (q ^ 2 + 1) ∧
    2 * f * q ^ 6 * (q ^ 2 - 1) ^ 2 < (q ^ 2 / 2).factorial ^ (q + 1) ∧
    2 * f * q ^ 10 * (q ^ 2 - 1) ^ 2 * (q ^ 3 + 1) <
      (q ^ 2 / 2).factorial ^ (q ^ 3 + 1) := by
  have hq1 : 1 < q := by omega
  have hq2 : 8 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq _
  have hq3 : 8 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq _
  have hF1 := le_half_factorial hq
  have hF2 := le_half_factorial (hq2.trans' (by decide : 8 ≤ 8 ^ 2))
  have hPower (k l : ℕ) (h : k < l) : q ^ k < (q / 2).factorial ^ l :=
    (Nat.pow_lt_pow_right hq1 h).trans_le (Nat.pow_le_pow_left hF1 _)
  have hPowerSq (k l : ℕ) (h : k < 2 * l) : q ^ k < (q ^ 2 / 2).factorial ^ l := by
    apply (Nat.pow_lt_pow_right hq1 h).trans_le
    rw [pow_mul]
    exact Nat.pow_le_pow_left hF2 _
  have hq4Bound : q ^ 3 + 1 ≤ q ^ 4 := by
    have hPos : 0 < q ^ 3 := Nat.pow_pos (by omega)
    calc
      q ^ 3 + 1 ≤ 2 * q ^ 3 := by omega
      _ ≤ q * q ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = q ^ 4 := (pow_succ' _ _).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (show f * q ^ 4 * (q - 1) * (q ^ 2 - 1) ≤ q ^ 8 from ?_).trans_lt
      (hPower 8 (q + 1) (by omega))
    calc
      _ ≤ q * q ^ 4 * q * q ^ 2 := by
        gcongr <;> exact Nat.sub_le _ _
      _ = _ := by ring
  · apply (show 2 * f * q ^ 6 * (q - 1) * (q ^ 4 - 1) ≤ q ^ 13 from ?_).trans_lt
      (hPower 13 (q ^ 2 + 1) (by omega))
    calc
      _ ≤ q * q * q ^ 6 * q * q ^ 4 := by
        gcongr <;> first | omega | exact Nat.sub_le _ _
      _ = _ := by ring
  · apply (show 2 * f * q ^ 6 * (q ^ 2 - 1) ^ 2 ≤ q ^ 12 from ?_).trans_lt
      (hPowerSq 12 (q + 1) (by omega))
    calc
      _ ≤ q * q * q ^ 6 * (q ^ 2) ^ 2 := by
        gcongr <;> first | omega | exact Nat.sub_le _ _
      _ = _ := by ring
  · apply (show 2 * f * q ^ 10 * (q ^ 2 - 1) ^ 2 * (q ^ 3 + 1) ≤ q ^ 20 from ?_).trans_lt
      (hPowerSq 20 (q ^ 3 + 1) (by omega))
    calc
      _ ≤ q * q * q ^ 10 * (q ^ 2) ^ 2 * q ^ 4 := by
        gcongr <;> first | omega | exact Nat.sub_le _ _
      _ = _ := by ring

/-- For the dual of the rank-two Hermitian geometry in dimension five,
the line-stabilizer order is smaller than the local factorial bound. -/
theorem unitaryFive_dual_stabilizer_bound (q f : ℕ) (hq : 2 ≤ q) (hf : f ≤ q) :
    2 * f * q ^ 10 * (q ^ 2 - 1) * (q ^ 4 - 1) <
      (q ^ 3 / 2).factorial ^ (q ^ 2 + 1) := by
  by_cases hTwo : q = 2
  · subst q
    exact (Nat.mul_le_mul_right 15 (Nat.mul_le_mul_right 3
      (Nat.mul_le_mul_right 1024 (Nat.mul_le_mul_left 2 hf)))).trans_lt (by decide)
  have hSquare : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega : 3 ≤ q) _
  have hCube : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq _
  have hFactorial := le_half_factorial hCube
  calc
    _ ≤ q * q * q ^ 10 * q ^ 2 * q ^ 4 := by
      gcongr <;> exact Nat.sub_le _ _
    _ = q ^ 18 := by ring
    _ < q ^ (3 * (q ^ 2 + 1)) := Nat.pow_lt_pow_right (by omega) (by omega)
    _ ≤ _ := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left hFactorial _

end EPPAIII.Primitive
