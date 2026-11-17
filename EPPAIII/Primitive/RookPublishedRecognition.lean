import EPPAIII.Primitive.PublishedRankThreeCoverage
import EPPAIII.Primitive.RankThree
import EPPAIII.Primitive.RookActionRecognition

/-! # The square product action in the published rank-three catalogue -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

private theorem rook_two_compl_not_connected : ¬ (rookGraph 2)ᶜ.Connected := by
  have hStep : ∀ a b c d : Fin 2, a ≠ c → b ≠ d → (a = b ↔ c = d) := by decide
  have hWalk {x y : Fin 2 × Fin 2} (w : (rookGraph 2)ᶜ.Walk x y) :
      x.1 = x.2 ↔ y.1 = y.2 := by
    induction w with
    | nil => rfl
    | @cons x z y hxz _ ih =>
      change x ≠ z ∧ ¬ (x ≠ z ∧ (x.1 = z.1 ∨ x.2 = z.2)) at hxz
      have h₁ : x.1 ≠ z.1 := fun h => hxz.2 ⟨hxz.1, Or.inl h⟩
      have h₂ : x.2 ≠ z.2 := fun h => hxz.2 ⟨hxz.1, Or.inr h⟩
      exact (hStep _ _ _ _ h₁ h₂).trans ih
  intro hConnected
  obtain ⟨w⟩ := hConnected.preconnected (0, 0) (0, 1)
  exact (by decide : (0 : Fin 2) ≠ 1) ((hWalk w).mp rfl)

/-- A primitive rank-three host with a square product-action labelling is
a rook graph or its complement. The two orientations exclude side length two. -/
theorem HasPublishedRankThreeModel.of_square_product_subgroup
    {V : Type*} {m : ℕ} (H : SimpleGraph V) (labels : V ≃ Fin m × Fin m)
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H)
    {P : Subgroup (Equiv.Perm (Fin m × Fin m))}
    (hOrbits : HasRankThreeGraphOrbits P (pullbackGraph H labels.symm))
    (hProduct : ∀ p : P, ∃ a b : Equiv.Perm (Fin m),
      p.val = a.prodCongr b ∨ p.val = (a.prodCongr b) * Equiv.prodComm _ _) :
    HasPublishedRankThreeModel H := by
  let K := pullbackGraph H labels.symm
  have hRankK := rankThree_pullback H labels.symm hRank
  have hm : 2 ≤ m := by
    obtain ⟨x, y, hxy⟩ := hRankK.1
    by_contra! hSmall
    apply hxy.ne
    apply Prod.ext <;> apply Fin.ext
    · have := x.1.isLt
      have := y.1.isLt
      omega
    · have := x.2.isLt
      have := y.2.isLt
      omega
  have hModel : K = rookGraph m ∨ K = (rookGraph m)ᶜ :=
    graph_eq_rook_or_compl_of_product_subgroup hm hOrbits hProduct hRankK.1 hRankK.2.1
  have hThree : 3 ≤ m := by
    by_contra! hSmall
    have hmTwo : m = 2 := by omega
    subst m
    obtain ⟨hConn, hConnC⟩ := primitive_rankThree_connected K
      (primitive_pullback_equiv H labels.symm hPrim) hRankK
    rcases hModel with hRook | hRook
    · exact rook_two_compl_not_connected (hRook ▸ hConnC)
    · exact rook_two_compl_not_connected (hRook ▸ hConn)
  let iso : K ≃g H := ⟨labels.symm, Iff.rfl⟩
  refine Or.inl ⟨m, hThree, ?_⟩
  rcases hModel with hRook | hRook
  · exact Or.inl ⟨hRook ▸ iso.symm⟩
  · exact Or.inr ⟨hRook ▸ iso.symm⟩

end EPPAIII.Primitive
