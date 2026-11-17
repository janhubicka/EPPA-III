import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify

/-! # Numerical bounds for the two subconstituents of bilinear forms graphs -/

namespace EPPAIII.Primitive

private theorem cubic_le_pow {q m : ℕ} (hq : 2 ≤ q) (hm : 3 ≤ m) :
    q ^ 3 ≤ q ^ m := Nat.pow_le_pow_right (by omega) hm

/-- The rank-one constituent has degree strictly below half its order minus one. -/
theorem bilinearForms_local_sparse {q m : ℕ} (hq : 2 ≤ q) (hm : 3 ≤ m) :
    2 * (q ^ m + (q - 2) * (q + 1)) + 2 < (q + 1) * (q ^ m - 1) := by
  generalize hx : q ^ m = x
  have hcubic : q ^ 3 ≤ x := hx ▸ cubic_le_pow hq hm
  have hq₁ : 1 ≤ q := by omega
  have hx₁ : 1 ≤ x := (Nat.one_le_pow 3 q hq₁).trans hcubic
  have hqz : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  zify [hq, hx₁] at hcubic ⊢
  have hsmall : 2 * (q : ℤ)^2 ≤ x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqz) (sq_nonneg (q : ℤ))]
  have hscale : (x : ℤ) ≤ ((q : ℤ) - 1) * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqz) (show 0 ≤ (x : ℤ) by positivity)]
  nlinarith

/-- For q at least three, the order of the rank-one constituent exceeds twice
the sum of its degree and the column-space bound for an independent set. -/
theorem bilinearForms_local_independence_gap {q m : ℕ} (hq : 3 ≤ q) (hm : 3 ≤ m) :
    2 * (q ^ m + (q - 2) * (q + 1) + (q + 1)) < (q + 1) * (q ^ m - 1) := by
  generalize hx : q ^ m = x
  have hq₂ : 2 ≤ q := by omega
  have hcubic : q ^ 3 ≤ x := hx ▸ cubic_le_pow hq₂ hm
  have hq₁ : 1 ≤ q := by omega
  have hx₁ : 1 ≤ x := (Nat.one_le_pow 3 q hq₁).trans hcubic
  have hqz : (3 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  zify [hq₂, hx₁] at hcubic ⊢
  have hsmall : 3 * (q : ℤ)^2 ≤ x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqz) (sq_nonneg (q : ℤ))]
  have hscale : (x : ℤ) ≤ ((q : ℤ) - 1) * x := by
    nlinarith [mul_nonneg (show 0 ≤ (q : ℤ) - 2 by omega)
      (show 0 ≤ (x : ℤ) by positivity)]
  have hquad : (q : ℤ) ≤ (q : ℤ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ (q : ℤ) by positivity)
      (show 0 ≤ (q : ℤ) - 1 by omega)]
  nlinarith

/-- The field-size and rank hypotheses imply the cutoff used in the uniform
rank-two argument, with just the binary three-column case excepted. -/
theorem bilinearForms_nonlocal_power_cutoff {q m : ℕ} (hq : 2 ≤ q) (hm : 3 ≤ m)
    (hExcept : q ≠ 2 ∨ m ≠ 3) : 3 * q + 6 ≤ q ^ m := by
  by_cases hq₂ : q = 2
  · subst q
    have h₄ : 4 ≤ m := by omega
    exact le_trans (show 3 * 2 + 6 ≤ (2 : ℕ) ^ 4 by decide)
      (Nat.pow_le_pow_right (by decide) h₄)
  · have hq₃ : 3 ≤ q := by omega
    have h₁ : 3 * q + 6 ≤ q ^ 3 := by
      have hq₉ : 9 ≤ q ^ 2 := by simpa using Nat.pow_le_pow_left hq₃ 2
      have hm₉ := Nat.mul_le_mul_left q hq₉
      nlinarith
    exact h₁.trans (cubic_le_pow hq hm)

/-- The rank-two constituent has an order greater than twice its degree plus
twice the first-row bound for an independent set, except in the binary small case. -/
theorem bilinearForms_nonlocal_independence_gap {q m : ℕ} (hq : 2 ≤ q) (hm : 3 ≤ m)
    (hExcept : q ≠ 2 ∨ m ≠ 3) :
    2 * ((q + 1) * (q ^ m - q - 1) + q ^ m) <
      (q ^ m)^2 - (q + 1) * q ^ m + q := by
  generalize hx : q ^ m = x
  have hlarge : 3 * q + 6 ≤ x := hx ▸ bilinearForms_nonlocal_power_cutoff hq hm hExcept
  have hqx : q ≤ x := by omega
  have hq₁x : 1 ≤ x - q := by omega
  have hsub : (q + 1) * x ≤ x^2 := by
    calc
      (q + 1) * x ≤ x * x := Nat.mul_le_mul_right _ (by omega)
      _ = x^2 := by rw [pow_two]
  zify [hqx, hq₁x, hsub] at hlarge ⊢
  have hprod := mul_nonneg (show 0 ≤ (x : ℤ) by positivity)
    (show 0 ≤ (x : ℤ) - (3 * (q : ℤ) + 5) by omega)
  nlinarith [sq_nonneg ((q : ℤ) + 1)]

end EPPAIII.Primitive
