import EPPAIII.BlockSystems.GardinerLiteralNormalization
import EPPAIII.Primitive.RookBounds

/-! # Gardiner's theorem on a finite index set -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems EPPAIII.DoubleCover

/-- The published finite homogeneous graph classification on nonempty
standard vertex sets. A single instance works in every vertex universe. -/
def FinGardinerRecognition : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ H : SimpleGraph (Fin n),
    IsHomogeneousGraph H → GardinerPublishedModels H

theorem gardinerPublishedModels_of_iso {A B : Type*} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (φ : G ≃g H)
    (hModel : GardinerPublishedModels G) : GardinerPublishedModels H := by
  have lift {X : Type*} {K : SimpleGraph X} (e : X ≃ A) (he : CanonicalBaseCopy K G e) :
      CanonicalBaseCopy K H (e.trans φ.toEquiv) :=
    fun x y => (he x y).trans φ.map_adj_iff.symm
  unfold GardinerPublishedModels at hModel ⊢
  rcases hModel with ⟨s, t, hs, ht, e, he⟩ | ⟨s, t, hs, ht, e, he⟩ |
    ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl ⟨s, t, hs, ht, _, lift e he⟩
  · exact Or.inr (Or.inl ⟨s, t, hs, ht, _, lift e he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨_, lift e he⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, lift e he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, lift e he⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, lift e he⟩))))

/-- Transport the one published premise to any nonempty finite vertex type. -/
theorem gardinerRecognition_of_fin (hGardiner : FinGardinerRecognition)
    {A : Type*} [Fintype A] (G : SimpleGraph A) (hNonempty : Nonempty A)
    (hHom : IsHomogeneousGraph G) : GardinerPublishedModels G := by
  let labels := (Fintype.equivFin A).symm
  let φ : pullbackGraph G labels ≃g G := ⟨labels, Iff.rfl⟩
  exact gardinerPublishedModels_of_iso φ
    (hGardiner (Fintype.card_pos_iff.mpr hNonempty) _ (homogeneous_graph_of_iso φ hHom))

end EPPAIII.Primitive
