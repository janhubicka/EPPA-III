import Mathlib

/-!
# Arithmetic behind the repaired Claim 3.9

The crucial numerical inequality is
  s * C(t,k) ≤ C(s,r) * C(t,k)^r ≤ s*t,
where r≥1 counts the coordinates whose neighbourhood size is k.

This module proves the *arithmetic* step for arbitrary parameters.
The group-theoretic lower bound
  C(s,r) * C(t,k)^r ≤ |Aut(sK_t) · P(w)|
is a separate, still unformalized orbit calculation.
The verified EPPA profile theorem gives the opposite bound.
-/

namespace EPPAIII.CliqueCovers

/-- Every nontrivial binomial coefficient is at least its row index. -/
theorem choose_ge_self (s : ℕ) :
    ∀ r : ℕ, 0 < r → r < s → s ≤ Nat.choose s r := by
  induction s with
  | zero =>
      intro r _ h
      omega
  | succ s ih =>
      intro r hr hlt
      cases r with
      | zero => omega
      | succ r =>
          cases r with
          | zero =>
              simp [Nat.choose_one_right]
          | succ r =>
              have hSmall : r + 1 < s := by omega
              have hOld : s ≤ Nat.choose s (r + 1) :=
                ih (r + 1) (by omega) hSmall
              have hExtra : 0 < Nat.choose s (Nat.succ (r + 1)) :=
                Nat.choose_pos (by omega)
              rw [Nat.choose_succ_succ s (r + 1)]
              omega

/-- Strict inequality for genuinely intermediate binomial entries. -/
theorem choose_gt_self_interior (t k : ℕ)
    (hk : 2 ≤ k) (hkt : k + 2 ≤ t) :
    t < Nat.choose t k := by
  cases t with
  | zero => omega
  | succ t =>
      have h₁ : t ≤ Nat.choose t (k - 1) :=
        choose_ge_self t (k - 1) (by omega) (by omega)
      have h₂ : t ≤ Nat.choose t k :=
        choose_ge_self t k (by omega) (by omega)
      rw [Nat.choose_succ_left t k (by omega)]
      omega

/-- An exponential with base at least two dominates shifted linear growth. -/
theorem power_dominates_succ (b r : ℕ) (hb : 2 ≤ b) :
    r + 1 ≤ b ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hMul : (r + 1) * 2 ≤ b ^ r * b :=
        Nat.mul_le_mul ih hb
      rw [pow_succ]
      omega

theorem base_le_power (b r : ℕ)
    (hb : 2 ≤ b) (hr : 0 < r) :
    b ≤ b ^ r := by
  cases r with
  | zero => omega
  | succ r =>
      have hOne : 1 ≤ b ^ r := by
        have hBound := power_dominates_succ b r hb
        omega
      have hMul := Nat.mul_le_mul_right b hOne
      simpa [pow_succ] using hMul

/-- The numerical lower bound, including r=s where C(s,r)=1. -/
theorem choose_power_ge_linear (s r b : ℕ)
    (hs : 0 < s) (hr : 0 < r) (hrs : r ≤ s)
    (hb : 2 ≤ b) :
    s * b ≤ Nat.choose s r * b ^ r := by
  by_cases hEq : r = s
  · subst r
    cases s with
    | zero => omega
    | succ s =>
        have hBound := power_dominates_succ b s hb
        have hMul := Nat.mul_le_mul_right b hBound
        simpa [pow_succ] using hMul
  · have hlt : r < s := by omega
    have hChoose : s ≤ Nat.choose s r :=
      choose_ge_self s r hr hlt
    have hPow : b ≤ b ^ r := base_le_power b r hb hr
    exact Nat.mul_le_mul hChoose hPow

/-- The numerical conclusion of the Claim 3.9 repair.
The wreath-orbit size lower bound is an explicit hypothesis, never
an axiom or a falsely certified graph-theoretic statement. -/
theorem only_singleton_or_cosingleton
    (s t r k : ℕ)
    (hs : 0 < s) (hr : 0 < r) (hrs : r ≤ s)
    (hk : 0 < k) (hkt : k < t)
    (hOrbitLowerUpper :
       Nat.choose s r * (Nat.choose t k) ^ r ≤ s * t) :
    k = 1 ∨ k + 1 = t := by
  have hChoose : t ≤ Nat.choose t k :=
    choose_ge_self t k hk hkt
  have hBase : 2 ≤ Nat.choose t k := by omega
  have hLinear :
      s * Nat.choose t k ≤
        Nat.choose s r * (Nat.choose t k) ^ r :=
    choose_power_ge_linear s r (Nat.choose t k)
      hs hr hrs hBase
  have hBound : s * Nat.choose t k ≤ s * t :=
    hLinear.trans hOrbitLowerUpper
  have hChooseLe : Nat.choose t k ≤ t :=
    Nat.le_of_mul_le_mul_left hBound hs
  by_contra hNo
  have hk₂ : 2 ≤ k := by omega
  have hkt₂ : k + 2 ≤ t := by omega
  have hStrict := choose_gt_self_interior t k hk₂ hkt₂
  omega

end EPPAIII.CliqueCovers
