import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Grassmann subconstituent arithmetic

The arithmetic uses `A = q^(n - 3)` and `Q = (q^2 * A - 1) / (q - 1)`.
For `n ≥ 5`, the natural-number parameters satisfy `q ≥ 2` and
`A ≥ q^2`. Rational inequalities keep all density bounds exact.
-/

namespace EPPAIII.Primitive

/-- The field-size and dimension assumptions imply the rational parameter bounds
for `A = q^(n - 3)`. -/
theorem grassmann_power_hypotheses {q n : ℕ} (hq : 2 ≤ q) (hn : 5 ≤ n) :
    (2 : ℚ) ≤ q ∧ (q : ℚ) ^ 2 ≤ (q : ℚ) ^ (n - 3) := by
  have hPower : q ^ 2 ≤ q ^ (n - 3) := Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨by exact_mod_cast hq, by exact_mod_cast hPower⟩

/-- The order minus twice the degree and twice the independent-set bound
for the first Grassmann subconstituent is positive. -/
theorem grassmann_first_degree_add_independence_lt_half
    (q A : ℚ) (hq : 2 ≤ q) (hA : q ^ 2 ≤ A) :
    let Q := (q ^ 2 * A - 1) / (q - 1)
    (Q + q ^ 2 - 2) + (q + 1) < ((q + 1) * (Q - 1)) / 2 := by
  dsimp
  have hDen : q - 1 ≠ 0 := by linarith
  have hRewrite : (q + 1) * ((q ^ 2 * A - 1) / (q - 1) - 1) -
      2 * (((q ^ 2 * A - 1) / (q - 1) + q ^ 2 - 2) + (q + 1)) =
        q ^ 2 * A - 2 * q ^ 2 - 3 * q := by
    field_simp
    ring
  let x := q - 2
  have hx : 0 ≤ x := sub_nonneg.mpr hq
  have hBase : 0 < q ^ 4 - 2 * q ^ 2 - 3 * q := by
    have hPos : 0 < x ^ 4 + 8 * x ^ 3 + 22 * x ^ 2 + 21 * x + 2 := by positivity
    convert hPos using 1
    dsimp [x]
    ring
  have hMul : q ^ 4 ≤ q ^ 2 * A := by
    calc
      q ^ 4 = q ^ 2 * q ^ 2 := by ring
      _ ≤ q ^ 2 * A := mul_le_mul_of_nonneg_left hA (sq_nonneg q)
  linarith

/-- A nonnegative-coefficient certificate for the cleared second
subconstituent inequality. The constant term is already positive at
`q = 2, A = 4`. -/
private theorem grassmann_second_cleared_gap_pos (q A : ℚ)
    (hq : 2 ≤ q) (hA : q ^ 2 ≤ A) :
    0 < q ^ 4 * (q * A - 1) * (A - 1) -
      (2 * (q ^ 2 - 1) * (q + 1) * (q ^ 2 * A - 1 - (q - 1) * (q + 2)) +
        2 * (q - 1) * (q ^ 3 * A - 1)) := by
  let x := q - 2
  let y := A - q ^ 2
  have hx : 0 ≤ x := sub_nonneg.mpr hq
  have hy : 0 ≤ y := sub_nonneg.mpr hA
  have hPos : 0 <
      76 + 658 * x + 2022 * x ^ 2 + 3190 * x ^ 3 + 2959 * x ^ 4 +
        1710 * x ^ 5 + 625 * x ^ 6 + 141 * x ^ 7 + 18 * x ^ 8 + x ^ 9 +
      y * (120 + 552 * x + 1010 * x ^ 2 + 964 * x ^ 3 + 525 * x ^ 4 +
        165 * x ^ 5 + 28 * x ^ 6 + 2 * x ^ 7) +
      y ^ 2 * (x + 2) ^ 5 := by positivity
  convert hPos using 1
  dsimp [x, y]
  ring

/-- The degree plus the independence bound for the second Grassmann
subconstituent is strictly below half its order, uniformly for `q ≥ 2`
and `A ≥ q^2`. -/
theorem grassmann_second_degree_add_independence_lt_half
    (q A : ℚ) (hq : 2 ≤ q) (hA : q ^ 2 ≤ A) :
    let Q := (q ^ 2 * A - 1) / (q - 1)
    (q + 1) * (Q - q - 2) + (q ^ 3 * A - 1) / (q ^ 2 - 1) <
      (q ^ 4 * (q * A - 1) * (A - 1) / ((q ^ 2 - 1) * (q - 1))) / 2 := by
  dsimp
  have hq1 : 0 < q - 1 := by linarith
  have hq2 : 0 < q ^ 2 - 1 := by nlinarith
  have hDen : 0 < 2 * ((q ^ 2 - 1) * (q - 1)) := by positivity
  have hLeft :
      ((q + 1) * ((q ^ 2 * A - 1) / (q - 1) - q - 2) +
        (q ^ 3 * A - 1) / (q ^ 2 - 1)) * (2 * ((q ^ 2 - 1) * (q - 1))) =
      2 * (q ^ 2 - 1) * (q + 1) * (q ^ 2 * A - 1 - (q - 1) * (q + 2)) +
        2 * (q - 1) * (q ^ 3 * A - 1) := by
    field_simp
    ring
  have hRight :
      (q ^ 4 * (q * A - 1) * (A - 1) / ((q ^ 2 - 1) * (q - 1))) / 2 *
        (2 * ((q ^ 2 - 1) * (q - 1))) =
      q ^ 4 * (q * A - 1) * (A - 1) := by
    field_simp
  refine lt_of_mul_lt_mul_right ?_ hDen.le
  rw [hLeft, hRight]
  exact sub_pos.mp (grassmann_second_cleared_gap_pos q A hq hA)

end EPPAIII.Primitive
