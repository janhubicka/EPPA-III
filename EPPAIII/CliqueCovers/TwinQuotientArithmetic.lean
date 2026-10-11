import Mathlib

/-!
# The final numerical rigidity of the true-twin quotient

In the zero-partial-profile case of Lemma 3.7, let:
* s be the number of selected cliques K_t;
* a be the common size of the true-twin classes;
* M be the number of quotient classes.

The quotient-fiber count gives M*a=2*s*t. The selected classes
have size at least t, hence t≤a. When the quotient has positive
degree, the regular independent-set inequality gives 2*s≤M.
The resulting arithmetic forces exactly a=t and M=2*s.

This independent Nat lemma isolates the final cancellation step,
without silently assuming graph quotient properties.
-/

namespace EPPAIII.CliqueCovers

/-- The quotient-size equations have a unique solution once the
selected classes fill at least half the regular quotient. -/
theorem twin_quotient_numerical_rigidity
    (s t a M : ℕ)
    (hs : 0 < s) (ht : 0 < t)
    (ha : t ≤ a)
    (hOrder : M * a = 2 * s * t)
    (hIndependent : 2 * s ≤ M) :
    M = 2 * s ∧ a = t := by
  have hMt : M * t ≤ (2 * s) * t := by
    calc
      M * t ≤ M * a := Nat.mul_le_mul_left M ha
      _ = (2 * s) * t := hOrder
  have hMle : M ≤ 2 * s :=
    Nat.le_of_mul_le_mul_right hMt ht
  have hMeq : M = 2 * s := by omega
  have hMa : M * a = M * t := by
    calc
      M * a = (2 * s) * t := hOrder
      _ = M * t := by rw [hMeq]
  have hMpos : 0 < M := by omega
  have hAle : a ≤ t :=
    Nat.le_of_mul_le_mul_left (le_of_eq hMa) hMpos
  exact ⟨hMeq, by omega⟩

end EPPAIII.CliqueCovers
