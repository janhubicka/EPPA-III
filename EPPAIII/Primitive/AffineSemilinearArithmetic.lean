import Mathlib.Data.Nat.Log
import Lean.Elab.Tactic.Omega

/-!
# The affine semilinear neighbourhood cutoff

For dimension at least four and field order at least three, the number of
adjacency profiles on an origin, a basis, and the necessary field anchors
is too small to accommodate half the host.
-/

namespace EPPAIII.Primitive

private theorem twice_binary_profiles_lt_ternary (d : ℕ) (hd : 4 ≤ d) :
    2 * (2 ^ (d + 1) + (d + 1)) < 3 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih =>
    rw [show d + 1 + 1 = (d + 1) + 1 from rfl, Nat.pow_succ 2 (d + 1), Nat.pow_succ 3 d]
    have hp : 0 < 2 ^ (d + 1) := Nat.pow_pos (by decide)
    omega

/-- The adjacency-profile bound is strictly below half the ambient order. -/
theorem affineSemilinear_twice_profile_lt_order
    (p r d : ℕ) (hp : 2 ≤ p) (hr : 0 < r) (hq : 3 ≤ p ^ r) (hd : 4 ≤ d) :
    2 * (2 ^ (d + Nat.log 2 r + 1) + (d + Nat.log 2 r + 1)) < (p ^ r) ^ d := by
  have hLog : Nat.log 2 r < r :=
    Nat.log_lt_of_lt_pow hr.ne' (Nat.lt_pow_self (by decide : 1 < 2))
  have hSize : d + Nat.log 2 r + 1 ≤ d + r := by omega
  have hBound : 2 * (2 ^ (d + Nat.log 2 r + 1) + (d + Nat.log 2 r + 1))
      ≤ 2 * (2 ^ (d + r) + (d + r)) :=
    Nat.mul_le_mul_left 2 (Nat.add_le_add (Nat.pow_le_pow_right (by decide) hSize) hSize)
  apply hBound.trans_lt
  by_cases hrOne : r = 1
  · subst r
    exact (twice_binary_profiles_lt_ternary d hd).trans_le (Nat.pow_le_pow_left hq d)
  have hrTwo : 2 ≤ r := by omega
  have hProduct : d + r + 2 ≤ r * d := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hd
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrTwo
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega
  have hStrict : 2 * (2 ^ (d + r) + (d + r)) < 2 ^ (d + r + 2) := by
    have hx : d + r < 2 ^ (d + r) := Nat.lt_pow_self (by decide)
    rw [Nat.pow_succ, Nat.pow_succ]
    omega
  calc
    _ < 2 ^ (d + r + 2) := hStrict
    _ ≤ 2 ^ (r * d) := Nat.pow_le_pow_right (by decide) hProduct
    _ = (2 ^ r) ^ d := Nat.pow_mul 2 r d
    _ ≤ (p ^ r) ^ d := Nat.pow_le_pow_left (Nat.pow_le_pow_left hp r) d

end EPPAIII.Primitive
