import EPPAIII.Primitive.AffineLineExclusion
import EPPAIII.Primitive.SmallConstituentCases
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness

/-! # The Paley hosts in the small-constituent screen -/

namespace EPPAIII.Primitive
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Turn the semilinear bound into the exclusion used by the finite screen. -/
theorem noHalfOrderEPPA_of_affineLine {K F : Type*}
    [Field K] [Field F] [Fintype F] [Algebra K F] [FiniteDimensional K F]
    (H : SimpleGraph F) (hAffine : HasAffineLineAction K H)
    (hOrder : 8 * Module.finrank K F + 4 < Nat.card F) : NoHalfOrderEPPA H := by
  apply (noHalfOrderEPPA_iff H).mpr
  intro S hLarge heppa
  exact (Nat.not_lt_of_ge
    (affineLine_host_order_bound (H.induce S) H _ heppa hLarge hAffine)) hOrder

/-- At a prime order the full affine action suffices for the Paley exclusion. -/
theorem noHalfOrderEPPA_paleyPrimeModel (q : ℕ) [Fact q.Prime] [NeZero q] (hLarge : 12 < q)
    (hAffine : ∀ f : Equiv.Perm (ZMod q), IsGraphAutomorphism (paleyPrimeModel q) f →
      ∃ a b : ZMod q, ∀ z, f z = a * z + b) :
    NoHalfOrderEPPA (paleyPrimeModel q) := by
  apply noHalfOrderEPPA_of_affineLine (K := ZMod q)
  · intro f hf
    obtain ⟨a, b, h⟩ := hAffine f hf
    exact ⟨a, b, AlgEquiv.refl, h⟩
  · simpa only [Module.finrank_self, Nat.card_eq_fintype_card, ZMod.card] using hLarge

/-- Supply the field presentation of Paley(25) and the full actions of the
four graphs in the screen. The exclusions then follow from the anchor bound. -/
theorem smallPaleyExclusions_of_affine_actions {F : Type*}
    [Field F] [Fintype F] [Algebra (ZMod 5) F] [FiniteDimensional (ZMod 5) F]
    (H : SimpleGraph F) (φ : paleyTwentyFiveModel ≃g H)
    (h₁₇ : ∀ f : Equiv.Perm (ZMod 17), IsGraphAutomorphism (paleyPrimeModel 17) f →
      ∃ a b : ZMod 17, ∀ z, f z = a * z + b)
    (h₃₇ : ∀ f : Equiv.Perm (ZMod 37), IsGraphAutomorphism (paleyPrimeModel 37) f →
      ∃ a b : ZMod 37, ∀ z, f z = a * z + b)
    (h₄₁ : ∀ f : Equiv.Perm (ZMod 41), IsGraphAutomorphism (paleyPrimeModel 41) f →
      ∃ a b : ZMod 41, ∀ z, f z = a * z + b)
    (h₂₅ : HasAffineLineAction (ZMod 5) H) : SmallPaleyExclusions := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  letI : Fact (Nat.Prime 37) := ⟨by decide⟩
  letI : Fact (Nat.Prime 41) := ⟨by decide⟩
  refine ⟨noHalfOrderEPPA_paleyPrimeModel 17 (by decide) h₁₇,
    noHalfOrderEPPA_paleyPrimeModel 37 (by decide) h₃₇,
    noHalfOrderEPPA_paleyPrimeModel 41 (by decide) h₄₁, ?_⟩
  have hCard : Nat.card F = 25 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, ZMod.card]
  have hPow := Module.card_eq_pow_finrank (K := ZMod 5) (V := F)
  rw [ZMod.card, ← Nat.card_eq_fintype_card (α := F), hCard] at hPow
  have hDegree := (Nat.pow_right_inj (by decide : 1 < 5)).mp
    (show 5 ^ Module.finrank (ZMod 5) F = 5 ^ 2 from hPow.symm)
  exact (noHalfOrderEPPA_of_affineLine H h₂₅ (by rw [hCard, hDegree]; decide)).of_iso φ

end EPPAIII.Primitive
