import EPPAIII.CliqueCovers.Claim39Arithmetic

/-!
# Arithmetic obstruction to multiple partial coordinates

The direct profile proof of Lemma 3.7 needs a second numerical fact:
when at least two coordinates have proper nonempty neighbourhoods, the
wreath-product orbit has at least C(s,p)*t^p elements, where p is the
number of such coordinates. This exceeds s*t except when s=t=p=2.

The *arithmetic* is proved here; the distinct-profile group-action
lower bound C(s,p)*t^p is a separate obligation. No custom axiom or
uncertified group-orbit claim is introduced in this module.
-/

namespace EPPAIII.CliqueCovers

/-- If at least two partial coordinates occur and their
combinatorial orbit lower bound is at most s*t, the only possible
parameters are the 2×2 exceptional configuration. -/
theorem multiple_partial_orbit_arithmetic
    (s t p : ℕ)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hp : 2 ≤ p) (hps : p ≤ s)
    (hOrbitBound : Nat.choose s p * t ^ p ≤ s * t) :
    s = 2 ∧ t = 2 ∧ p = 2 := by
  by_cases hlt : p < s
  · have hChoose : s ≤ Nat.choose s p :=
      choose_ge_self s p (by omega) hlt
    have hPow : t ^ 2 ≤ t ^ p :=
      Nat.pow_le_pow_right (by omega) hp
    have hProd : s * t ^ 2 ≤ Nat.choose s p * t ^ p :=
      Nat.mul_le_mul hChoose hPow
    have hStrict : t < t ^ 2 := by
      rw [pow_two]
      nlinarith
    have hStrictProd : s * t < s * t ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hStrict (by omega)
    omega
  · have heq : p = s := by omega
    subst p
    simp only [Nat.choose_self, one_mul] at hOrbitBound
    by_cases hMore : 3 ≤ s
    · have hExpBound : s - 1 ≤ t ^ (s - 2) := by
        have hpow := power_dominates_succ t (s - 2) ht
        omega
      have hProd :
          (s - 1) * t ≤ t ^ (s - 2) * t :=
        Nat.mul_le_mul_right t hExpBound
      have hPowerEq : t ^ (s - 2) * t = t ^ (s - 1) := by
        rw [← pow_succ]
        congr 1
        omega
      have hPowBound : (s - 1) * t ≤ t ^ (s - 1) :=
        hProd.trans_eq hPowerEq
      have hStrict : s < (s - 1) * t := by
        have hTwice : (s - 1) * 2 ≤ (s - 1) * t :=
          Nat.mul_le_mul_left (s - 1) ht
        omega
      have hGt : s < t ^ (s - 1) :=
        hStrict.trans_le hPowBound
      have hGtTimes : s * t < t ^ (s - 1) * t :=
        Nat.mul_lt_mul_of_pos_right hGt (by omega)
      have hPowerEq2 : t ^ (s - 1) * t = t ^ s := by
        rw [← pow_succ]
        congr 1
        omega
      have hStrictOrb : s * t < t ^ s :=
        hGtTimes.trans_eq hPowerEq2
      omega
    · have hs2 : s = 2 := by omega
      subst s
      have ht2 : t = 2 := by
        rw [pow_two] at hOrbitBound
        nlinarith
      subst t
      exact ⟨rfl, rfl, rfl⟩

end EPPAIII.CliqueCovers
