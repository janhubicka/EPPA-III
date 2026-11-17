import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic

/-! # Lower bounds for products of clique factorials -/

namespace EPPAIII.Primitive

open scoped BigOperators

private theorem factorial_le_mul_pow (a d : ℕ) :
    (a + d).factorial ≤ a.factorial * (a + d) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.add_succ, Nat.factorial_succ, pow_succ']
    calc
      (a + d + 1) * (a + d).factorial ≤
          (a + d + 1) * (a.factorial * (a + d) ^ d) :=
        Nat.mul_le_mul_left _ ih
      _ ≤ (a + d + 1) * (a.factorial * (a + d + 1) ^ d) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) d))
      _ = a.factorial * ((a + d + 1) * (a + d + 1) ^ d) := by ac_rfl

private theorem factorial_support (a m : ℕ) :
    m.factorial * m ^ a ≤ a.factorial * m ^ m := by
  by_cases h : m ≤ a
  · rw [← Nat.sub_add_cancel h, pow_add, ← mul_assoc]
    rw [Nat.sub_add_cancel h]
    exact Nat.mul_le_mul_right _ (Nat.factorial_mul_pow_sub_le_factorial h)
  · have ha : a ≤ m := by omega
    calc
      m.factorial * m ^ a ≤ (a.factorial * m ^ (m - a)) * m ^ a := by
        apply Nat.mul_le_mul_right
        simpa only [Nat.add_sub_of_le ha] using factorial_le_mul_pow a (m - a)
      _ = a.factorial * m ^ m := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel ha]

/-- A product of factorials lies above the factorial of any integer lower
bound on the average, raised to the number of factors. -/
theorem factorial_pow_card_le_prod_of_average {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    {m : ℕ} (hm : 0 < m) (hSum : s.card * m ≤ ∑ i ∈ s, a i) :
    m.factorial ^ s.card ≤ ∏ i ∈ s, (a i).factorial := by
  have hStep : ∏ i ∈ s, (m.factorial * m ^ a i) ≤
      ∏ i ∈ s, ((a i).factorial * m ^ m) :=
    Finset.prod_le_prod (fun i _ => factorial_support (a i) m)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_const, Finset.prod_pow_eq_pow_sum, ← pow_mul, mul_comm m s.card] at hStep
  have hmPower : m ^ (s.card * m) ≤ m ^ (∑ i ∈ s, a i) :=
    Nat.pow_le_pow_right hm hSum
  exact Nat.le_of_mul_le_mul_right ((Nat.mul_le_mul_left _ hmPower).trans hStep) (Nat.pow_pos hm)


private theorem two_pow_le_twice_factorial (a : ℕ) : 2 ^ a ≤ 2 * a.factorial := by
  induction a with
  | zero => simp
  | succ a ih =>
    cases a with
    | zero => decide
    | succ a =>
      rw [pow_succ', Nat.factorial_succ]
      exact (Nat.mul_le_mul_left 2 ih).trans
        (by simpa only [mul_assoc] using
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (a + 1).factorial
            (show 2 ≤ a + 1 + 1 by omega)))

/-- Each nonempty clique of order `a` contributes at least `2^(a-1)`
permutations. An empty clique also satisfies the bound with truncation. -/
theorem two_pow_le_clique_factorial_prod {ι : Type*} (s : Finset ι) (a : ι → ℕ)
    {m : ℕ} (hSize : s.card + m ≤ ∑ i ∈ s, a i) :
    2 ^ m ≤ ∏ i ∈ s, (a i).factorial := by
  have hProd : ∏ i ∈ s, (2 ^ a i : ℕ) ≤ ∏ i ∈ s, (2 * (a i).factorial) :=
    Finset.prod_le_prod (fun i _ => two_pow_le_twice_factorial (a i))
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_mul_distrib, Finset.prod_const] at hProd
  have hPow := (Nat.pow_le_pow_right (by decide : 0 < 2) hSize).trans hProd
  rw [pow_add] at hPow
  exact Nat.le_of_mul_le_mul_left hPow (Nat.pow_pos (by decide))

end EPPAIII.Primitive
