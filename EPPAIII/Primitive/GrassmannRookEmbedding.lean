import EPPAIII.Primitive.GrassmannGraph
import EPPAIII.Primitive.RookModel

/-! # An induced three-by-three grid in the first Grassmann constituent -/

namespace EPPAIII.Primitive

open Module
open scoped BigOperators

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private noncomputable def projectiveThree [Finite F] [FiniteDimensional F V]
    (hDim : 2 ≤ finrank F V) : Fin 3 ↪ Projectivization F V := by
  classical
  letI : Finite V := Module.finite_of_finite F
  letI := Fintype.ofFinite (Projectivization F V)
  have hSum : (∑ i ∈ Finset.range 2, Nat.card F ^ i) ≤
      ∑ i ∈ Finset.range (finrank F V), Nat.card F ^ i :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hDim)
  have hField : 1 < Nat.card F := Finite.one_lt_card
  have hCard : 3 ≤ Fintype.card (Projectivization F V) := by
    rw [← Nat.card_eq_fintype_card, Projectivization.card_of_finrank F V rfl]
    have hs : (∑ i ∈ Finset.range 2, Nat.card F ^ i) = Nat.card F + 1 := by simp
    omega
  exact (Fin.castLEEmb hCard).trans (Fintype.equivFin _).symm.toEmbedding

private theorem finrank_prod_submodule {X Y : Type*}
    [AddCommGroup X] [Module F X] [FiniteDimensional F X]
    [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
    (A : Submodule F X) (B : Submodule F Y) :
    finrank F (A.prod B) = finrank F A + finrank F B :=
  (A.prodEquiv B).finrank_eq.trans Module.finrank_prod

private theorem finrank_projective_inf [FiniteDimensional F V]
    (a b : Projectivization F V) [Decidable (a = b)] :
    finrank F (a.submodule ⊓ b.submodule : Submodule F V) =
      if a = b then 1 else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [Projectivization.finrank_submodule]
  · have hStrict : (a.submodule ⊓ b.submodule : Submodule F V) < a.submodule := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro e
      exact h (Projectivization.submodule_injective
        (Submodule.eq_of_le_of_finrank_le (e ▸ inf_le_right) (by
          rw [Projectivization.finrank_submodule, Projectivization.finrank_submodule])))
    have hRank := Submodule.finrank_lt_finrank_of_lt hStrict
    rw [Projectivization.finrank_submodule] at hRank
    simp only [if_neg h]
    omega

/-- Choosing three lines in the root and in a complement gives an induced rook graph. -/
noncomputable def grassmannGraph_local_rookThree [Finite F] [FiniteDimensional F V]
    (root : GrassmannPlane F V) (hDim : 4 ≤ finrank F V) :
    rookGraph 3 ↪g (grassmannGraph F V).induce ((grassmannGraph F V).neighborSet root) := by
  classical
  let W := (Submodule.exists_isCompl root.val).choose
  have hW : IsCompl root.val W := (Submodule.exists_isCompl root.val).choose_spec
  let e := root.val.prodEquivOfIsCompl W hW
  have hWdim : 2 ≤ finrank F W := by
    have h := e.finrank_eq
    rw [Module.finrank_prod, root.property] at h
    omega
  let left := projectiveThree (show 2 ≤ finrank F root.val from root.property.ge)
  let right := projectiveThree hWdim
  let P (i : Fin 3 × Fin 3) : Submodule F (root.val × W) :=
    (left i.1).submodule.prod (right i.2).submodule
  let P' (i : Fin 3 × Fin 3) : GrassmannPlane F V :=
    ⟨(P i).map e, by
      rw [e.finrank_map_eq, finrank_prod_submodule,
        Projectivization.finrank_submodule, Projectivization.finrank_submodule]⟩
  have hRoot : (Submodule.prod ⊤ ⊥ : Submodule F (root.val × W)).map e = root.val := by
    rw [Submodule.coe_prodEquivOfIsCompl, Submodule.map_coprod_prod, Submodule.map_bot,
      sup_bot_eq, ← LinearMap.range_eq_map, Submodule.range_subtype]
  have hLocal (i : Fin 3 × Fin 3) :
      (grassmannGraph F V).Adj root (P' i) := by
    change finrank F (root.val ⊓ (P i).map e : Submodule F V) = 1
    rw [← hRoot, ← Submodule.map_inf _ e.injective, e.finrank_map_eq]
    change finrank F ((Submodule.prod ⊤ ⊥ : Submodule F (root.val × W)) ⊓
      (left i.1).submodule.prod (right i.2).submodule) = 1
    rw [Submodule.prod_inf_prod, top_inf_eq, bot_inf_eq, finrank_prod_submodule,
      Projectivization.finrank_submodule, finrank_bot, add_zero]
  have hInj : Function.Injective P' := by
    intro i j h
    have he : P i = P j := Submodule.map_injective_of_injective e.injective
      (congrArg Subtype.val h)
    apply Prod.ext
    · apply left.injective
      apply Projectivization.submodule_injective
      simpa only [P, Submodule.prod_map_fst] using
        congrArg (Submodule.map (LinearMap.fst F root.val W)) he
    · apply right.injective
      apply Projectivization.submodule_injective
      simpa only [P, Submodule.prod_map_snd] using
        congrArg (Submodule.map (LinearMap.snd F root.val W)) he
  refine ⟨⟨fun i => ⟨P' i, hLocal i⟩, fun _ _ h => hInj (congrArg Subtype.val h)⟩, ?_⟩
  intro i j
  change finrank F ((P i).map e ⊓ (P j).map e : Submodule F V) = 1 ↔
    i ≠ j ∧ (i.1 = j.1 ∨ i.2 = j.2)
  rw [← Submodule.map_inf _ e.injective, e.finrank_map_eq]
  change finrank F ((left i.1).submodule.prod (right i.2).submodule ⊓
    (left j.1).submodule.prod (right j.2).submodule) = 1 ↔ _
  rw [Submodule.prod_inf_prod, finrank_prod_submodule, finrank_projective_inf, finrank_projective_inf]
  simp only [left.injective.eq_iff, right.injective.eq_iff]
  by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2
  · simp [Prod.ext h1 h2, h1, h2]
  · simp [h1, h2, fun h : i = j => h2 (congrArg Prod.snd h)]
  · simp [h1, h2, fun h : i = j => h1 (congrArg Prod.fst h)]
  · simp [h1, h2]

end EPPAIII.Primitive
