import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.Ring.Nat
import Lean.Elab.Tactic.Omega

/-! # Order and parity in the bilinear constituent reduction -/

namespace EPPAIII.Primitive

/-- Both bilinear constituent orders exceed the small homogeneous orders.
The rank-one order is even exactly for odd q. The rank-two order is even. -/
theorem bilinear_constituent_order_parity {q m : ℕ} (hq : 2 ≤ q) (hm : 3 ≤ m) :
    9 < (q + 1) * (q ^ m - 1) ∧ 9 < (q ^ m - 1) * (q ^ m - q) ∧
      (Even ((q + 1) * (q ^ m - 1)) ↔ ¬ Even q) ∧ Even ((q ^ m - 1) * (q ^ m - q)) := by
  have hqSq : 4 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hqCube : 4 * q ≤ q ^ 3 := by
    rw [pow_succ]
    exact Nat.mul_le_mul_right q hqSq
  have hlarge : q + 6 ≤ q ^ m := by
    calc
      q + 6 ≤ 4 * q := by omega
      _ ≤ q ^ 3 := hqCube
      _ ≤ q ^ m := Nat.pow_le_pow_right (by omega) hm
  have hBase : 7 ≤ q ^ m - 1 := by omega
  have hPow : Even (q ^ m) ↔ Even q := Nat.even_pow' (by omega : m ≠ 0)
  refine ⟨lt_of_lt_of_le (show 9 < 3 * 7 by decide) (Nat.mul_le_mul (by omega) hBase),
    lt_of_lt_of_le (show 9 < 7 * 6 by decide) (Nat.mul_le_mul hBase (by omega)), ?_, ?_⟩
  · rw [Nat.even_mul, Nat.even_add_one, Nat.even_sub (show 1 ≤ q ^ m by omega), hPow]
    simp
  · have hGap : Even (q ^ m - q) := (Nat.even_sub (show q ≤ q ^ m by omega)).mpr hPow
    exact Nat.even_mul.mpr (Or.inr hGap)

end EPPAIII.Primitive
