import EPPAIII.Primitive.StabilizerBase
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# The coordinate field in the semilinear stabilizer argument

Once a basis is fixed, a semilinear transformation is determined by its
field automorphism on the coordinates. The generated coordinate field is
either proper, giving the cardinality bound, or the whole field, giving
a small set of additional anchors.
-/

namespace EPPAIII.Primitive

/-- This is the coordinate-field step of the geometric stabilizer lemma.
The integer inequality in the first alternative expresses the square-root
bound without using real powers. -/
theorem proper_coordinate_field_or_small_galois_base
    {F K : Type*} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]
    [FiniteDimensional F K]
    (n : Nat) (S : Set (Fin n → K)) :
    (∃ E : IntermediateField F K, E ≠ ⊤ ∧
      (∀ x ∈ S, ∀ i, x i ∈ E) ∧ Nat.card S ^ 2 ≤ Fintype.card K ^ n) ∨
    (∃ U : Finset (Fin n → K), (U : Set (Fin n → K)) ⊆ S ∧
      U.card ≤ Nat.log 2 (Module.finrank F K) ∧
      ∀ g : K ≃ₐ[F] K, (∀ x ∈ U, ∀ i, g (x i) = x i) → ∀ a : K, g a = a) := by
  classical
  let C : Set K := {a | ∃ x ∈ S, ∃ i, x i = a}
  let E := IntermediateField.adjoin F C
  have hMem (x : Fin n → K) (hx : x ∈ S) (i : Fin n) : x i ∈ E :=
    IntermediateField.subset_adjoin F C ⟨x, hx, i, rfl⟩
  by_cases hE : E = ⊤
  · right
    letI : Finite (K ≃ₐ[F] K) :=
      Finite.of_injective (fun f : K ≃ₐ[F] K => (f : K → K)) DFunLike.coe_injective
    obtain ⟨U, hU, hSize, hFix⟩ :=
      exists_stabilizer_base_within (⊤ : Subgroup (K ≃ₐ[F] K)) S
    rw [Subgroup.card_top] at hSize
    have hGalCard : Nat.card (K ≃ₐ[F] K) ≤ Module.finrank F K := by
      rw [Nat.card_eq_fintype_card]
      exact AlgEquiv.card_le
    refine ⟨U, hU, hSize.trans (Nat.log_mono_right hGalCard), ?_⟩
    intro g hg
    have hCoordinates : ∀ t ∈ C, g • t = t := by
      rintro _ ⟨x, hx, i, rfl⟩
      exact congrFun (hFix g (Subgroup.mem_top g) (fun x hx => funext (hg x hx)) x hx) i
    have hField := (IntermediateField.forall_mem_adjoin_smul_eq_self_iff F g).mpr hCoordinates
    intro a
    exact hField a (show a ∈ E by rw [hE]; exact IntermediateField.mem_top)
  · left
    refine ⟨E, hE, hMem, ?_⟩
    letI : Fintype E := Fintype.ofFinite E
    let toE : S → Fin n → E := fun x i => ⟨x.val i, hMem x.val x.property i⟩
    have hInj : Function.Injective toE := by
      intro x y hxy
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (congrFun hxy i)
    have hCard := Fintype.card_le_of_injective toE hInj
    rw [← Nat.card_eq_fintype_card, Fintype.card_pi_const] at hCard
    have hDegree : 2 ≤ Module.finrank E K := by
      have hPositive : 0 < Module.finrank E K := Module.finrank_pos
      have hNeOne : Module.finrank E K ≠ 1 :=
        fun h => hE (IntermediateField.finrank_eq_one_iff_eq_top.mp h)
      omega
    have hFieldCard : Fintype.card E ^ 2 ≤ Fintype.card K := by
      rw [Module.card_eq_pow_finrank (K := E) (V := K)]
      exact Nat.pow_le_pow_right Fintype.card_pos hDegree
    calc
      Nat.card S ^ 2 ≤ (Fintype.card E ^ n) ^ 2 := Nat.pow_le_pow_left hCard _
      _ = (Fintype.card E ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]
      _ ≤ Fintype.card K ^ n := Nat.pow_le_pow_left hFieldCard _

end EPPAIII.Primitive
