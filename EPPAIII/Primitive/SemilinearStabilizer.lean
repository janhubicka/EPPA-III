import EPPAIII.Primitive.FieldCoordinateStabilizer
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Small pointwise stabilizers for semilinear transformations

The basis is chosen from the selected set itself. The coordinate-field
argument adds at most the base-two logarithm of the field extension degree
many selected points, unless a proper field already contains all the
coordinates in that basis.
-/

namespace EPPAIII.Primitive

open Submodule

theorem proper_subfield_or_semilinear_stabilizer_base
    {F K V : Type*} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]
    [FiniteDimensional F K]
    [AddCommGroup V] [Module K V] (S : Set V) [Module.Finite K (span K S)] :
    let d := Module.finrank K (span K S)
    (∃ E : IntermediateField F K, E ≠ ⊤ ∧
      ∃ b : Fin d → V, (∀ i, b i ∈ S) ∧ LinearIndependent K b ∧
        span K (Set.range b) = span K S ∧
        (∀ x ∈ S, ∃ t : Fin d → E, x = ∑ i, (t i : K) • b i) ∧
        Nat.card S ^ 2 ≤ Fintype.card K ^ d) ∨
    (∃ U : Finset V, (U : Set V) ⊆ S ∧
      U.card ≤ d + Nat.log 2 (Module.finrank F K) ∧
      ∀ g : K ≃ₐ[F] K, ∀ f : V →ₛₗ[RingHomClass.toRingHom g] V,
        (∀ x ∈ U, f x = x) → ∀ x ∈ span K S, f x = x) := by
  classical
  dsimp only
  let d := Module.finrank K (span K S)
  obtain ⟨b, hb, hbSpan, hbIndep⟩ := Submodule.exists_fun_fin_finrank_span_eq K S
  let Y := span K (Set.range b)
  let B : Module.Basis (Fin d) K Y := Module.Basis.span hbIndep
  have hMemY (x : V) (h : x ∈ span K S) : x ∈ Y := by
    change x ∈ span K (Set.range b)
    rwa [hbSpan]
  let coordinates (x : S) : Fin d → K :=
    B.equivFun ⟨x.val, hMemY x.val (subset_span x.property)⟩
  have hCoordinatesInj : Function.Injective coordinates := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun y : Y => y.val) (B.equivFun.injective h)
  let T := Set.range coordinates
  let C := Equiv.ofInjective coordinates hCoordinatesInj
  let vector (t : Fin d → K) : V := (B.equivFun.symm t).val
  have hExpansion (t : Fin d → K) : vector t = ∑ i, t i • b i := by
    change ((B.equivFun.symm t : Y) : V) = _
    rw [B.equivFun_symm_apply]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (B i : V) = b i from Module.Basis.coe_span_apply hbIndep i]
  have hRestore (x : S) : vector (coordinates x) = x.val := by
    change ((B.equivFun.symm (B.equivFun ⟨x.val, _⟩) : Y) : V) = x.val
    rw [B.equivFun.symm_apply_apply]
  rcases proper_coordinate_field_or_small_galois_base (F := F) d T with
    ⟨E, hProper, hMem, hCard⟩ | ⟨U, hU, hSize, hFix⟩
  · left
    refine ⟨E, hProper, b, hb, hbIndep, hbSpan, ?_, ?_⟩
    · intro x hx
      let y : S := ⟨x, hx⟩
      refine ⟨fun i => ⟨coordinates y i, hMem (coordinates y) ⟨y, rfl⟩ i⟩, ?_⟩
      exact (hRestore y).symm.trans (hExpansion (coordinates y))
    · have hST : Nat.card S = Nat.card T := Nat.card_congr C
      rw [hST]
      exact hCard
  · right
    let U' : Finset V := (Finset.univ.image b) ∪ (U.image vector)
    refine ⟨U', ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact hb i
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨y, rfl⟩ := hU ht
        rw [hRestore y]
        exact y.property
    · calc
        U'.card ≤ (Finset.univ.image b).card + (U.image vector).card :=
          Finset.card_union_le _ _
        _ ≤ d + Nat.log 2 (Module.finrank F K) := by
          have hn : (Finset.univ.image b).card ≤ d := by
            exact Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
          have hAdd : (U.image vector).card ≤ Nat.log 2 (Module.finrank F K) :=
            Finset.card_image_le.trans hSize
          exact Nat.add_le_add hn hAdd
    · intro g f hf
      have hBasis (i : Fin d) : f (b i) = b i :=
        hf _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
      have hAction (t : Fin d → K) : f (vector t) = vector (fun i => g (t i)) := by
        rw [hExpansion, hExpansion, map_sum]
        simp only [LinearMap.map_smulₛₗ, hBasis]
        rfl
      have hCoeff : ∀ t ∈ U, ∀ i, g (t i) = t i := by
        intro t ht i
        have htFix : f (vector t) = vector t :=
          hf _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ht))
        have hEq := (hAction t).symm.trans htFix
        exact congrFun (B.equivFun.symm.injective (Subtype.ext hEq)) i
      have hGal := hFix g hCoeff
      intro x hx
      let y : Y := ⟨x, hMemY x hx⟩
      have hRecon : vector (B.equivFun y) = x := by
        change ((B.equivFun.symm (B.equivFun y) : Y) : V) = _
        rw [B.equivFun.symm_apply_apply]
      have hId : (fun i => g (B.equivFun y i)) = B.equivFun y := funext (fun i => hGal _)
      rw [← hRecon, hAction, hId]

end EPPAIII.Primitive
