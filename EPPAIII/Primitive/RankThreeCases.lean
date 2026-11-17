import EPPAIII.Primitive.BipartitionTenExclusion
import EPPAIII.Primitive.OrthogonalEightConstituents

/-! # The resolved branches of the primitive rank-three catalogue -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers

private def localIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (r : V) : localGraph G r ≃g localGraph H (φ r) where
  toEquiv := φ.mapNeighborSet r
  map_rel_iff' := φ.map_adj_iff

private def nonlocalIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (r : V) : nonlocalGraph G r ≃g nonlocalGraph H (φ r) where
  toEquiv := φ.toEquiv.subtypeEquiv fun x =>
    and_congr (not_congr φ.injective.eq_iff.symm) φ.map_adj_iff.symm.not
  map_rel_iff' := φ.map_adj_iff

private def localComplIso {V : Type*} (G : SimpleGraph V) (r : V) :
    localGraph Gᶜ r ≃g (nonlocalGraph G r)ᶜ where
  toEquiv := Equiv.refl _
  map_rel_iff' := and_congr (not_congr Subtype.val_injective.eq_iff.symm) Iff.rfl

private def nonlocalComplIso {V : Type*} (G : SimpleGraph V) (r : V) :
    nonlocalGraph Gᶜ r ≃g (localGraph G r)ᶜ where
  toEquiv := (Equiv.refl V).subtypeEquiv fun x => by
    change (r ≠ x ∧ ¬ (r ≠ x ∧ ¬ G.Adj r x)) ↔ G.Adj r x
    exact ⟨fun ⟨hne, h⟩ => Classical.byContradiction fun hn => h ⟨hne, hn⟩,
      fun h => ⟨h.ne, fun hn => hn.2 h⟩⟩
  map_rel_iff' := by
    intro a b
    change (_ ≠ _ ∧ ¬ G.Adj a.val b.val) ↔
      (a.val ≠ b.val ∧ ¬ G.Adj a.val b.val)
    exact and_congr (not_congr ⟨fun h => congrArg Subtype.val h, Subtype.ext⟩) Iff.rfl

private theorem transitive_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (h : HasTransitiveGraphAutomorphisms G) :
    HasTransitiveGraphAutomorphisms H := by
  intro a b
  obtain ⟨q, hq, hab⟩ := h (φ.symm a) (φ.symm b)
  refine ⟨(φ.toEquiv.symm.trans q).trans φ.toEquiv, ?_, ?_⟩
  · intro x y
    exact φ.symm.map_adj_iff.symm.trans ((hq _ _).trans φ.map_adj_iff.symm)
  · change φ (q (φ.symm a)) = b
    rw [hab, φ.apply_symm_apply]

private theorem model_form_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (h : HasCliqueUnionOrCoverModel G) :
    HasCliqueUnionOrCoverModel H := by
  have move {U : Type*} {K : SimpleGraph U} (hK : IsModelUpToComplement G K) :
      IsModelUpToComplement H K := by
    rcases hK with hK | hK
    · obtain ⟨ψ⟩ := hK
      exact Or.inl ⟨φ.symm.trans ψ⟩
    · obtain ⟨ψ⟩ := hK
      exact Or.inr ⟨φ.symm.trans ψ⟩
  rcases h with ⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩
  · exact Or.inl ⟨s, t, move h⟩
  · exact Or.inr ⟨s, t, X, Y, move h⟩

private theorem model_form_of_compl {V : Type*} {G : SimpleGraph V}
    (h : HasCliqueUnionOrCoverModel Gᶜ) : HasCliqueUnionOrCoverModel G := by
  have move {U : Type*} {K : SimpleGraph U} (hK : IsModelUpToComplement Gᶜ K) :
      IsModelUpToComplement G K := by
    rcases hK with hK | hK
    · obtain ⟨ψ⟩ := hK
      exact Or.inr ⟨by simpa only [compl_compl] using complHostIso ψ⟩
    · obtain ⟨ψ⟩ := hK
      exact Or.inl ⟨by simpa only [compl_compl] using complHostIso ψ⟩
  rcases h with ⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩
  · exact Or.inl ⟨s, t, move h⟩
  · exact Or.inr ⟨s, t, X, Y, move h⟩

/-- The order-120 graph and its complement violate the Section 8
constituent-shape requirement at every root, in any labelling. -/
theorem orthogonalEight_model_excludes_forms {W : Type*} {H : SimpleGraph W}
    (hTrans : HasTransitiveGraphAutomorphisms H)
    (hModel : IsModelUpToComplement H nonsingularOrthogonalEightGraph) (root : W) :
    ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) := by
  rcases hModel with hModel | hModel
  · obtain ⟨φ⟩ := hModel
    obtain ⟨hL, hN⟩ := orthogonalEight_constituents_exclude_forms
      (transitive_of_iso φ hTrans) (φ root)
    exact ⟨fun h => hL (model_form_of_iso (localIso φ root) h),
      fun h => hN (model_form_of_iso (nonlocalIso φ root) h)⟩
  · obtain ⟨φ⟩ := hModel
    have hT : HasTransitiveGraphAutomorphisms nonsingularOrthogonalEightGraph := by
      simpa only [compl_compl] using
        transitive_complement nonsingularOrthogonalEightGraphᶜ (transitive_of_iso φ hTrans)
    obtain ⟨hL, hN⟩ := orthogonalEight_constituents_exclude_forms hT (φ root)
    refine ⟨fun h => hN (model_form_of_compl ?_), fun h => hL (model_form_of_compl ?_)⟩
    · exact model_form_of_iso (localComplIso _ _) (model_form_of_iso (localIso φ root) h)
    · exact model_form_of_iso (nonlocalComplIso _ _) (model_form_of_iso (nonlocalIso φ root) h)

/-- Once the Section 8 shape premise is supplied in the order-120 case,
only the separate model families in the external catalogue remain.
The rook and triangular conclusions retain the actual embedding. -/
theorem primitiveCases_or_residual_rankThree_model
    {V W : Type*} [Finite V] [Finite W]
    (catalog : RankThreeCatalog) (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hRank : HasRankThreeAutAction H) (hEppa : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (hModel : InRankThreeCatalog catalog H)
    (hOrthogonal : OrthogonalSearchChecks) (root : W)
    (hShape : IsModelUpToComplement H nonsingularOrthogonalEightGraph →
      HasCliqueUnionOrCoverModel (localGraph H root) ∨
        HasCliqueUnionOrCoverModel (nonlocalGraph H root)) :
    primitiveCases G H e ∨
      (∃ c : RankThreeExternalCase, ∃ model ∈ catalog c, IsModelUpToComplement H model.2) := by
  rcases hModel with ⟨n, hn, hRook⟩ | ⟨n, hn, hTri⟩ | hBipThree | hBipFour | hOrtho | hOther
  · exact Or.inl (primitiveCases_of_rook_model G H e hEppa hHalf n hn hRook)
  · left
    rcases hTri with hTri | hTri
    · obtain ⟨φ⟩ := hTri
      exact Or.inl (Or.inr (Or.inl (triangularPair_of_eppa G H e hHalf hEppa n hn φ)))
    · obtain ⟨φ⟩ := hTri
      have φ' : Hᶜ ≃g triangularModel n := by
        simpa only [compl_compl] using complHostIso φ
      exact Or.inr (Or.inr (Or.inl (triangularPair_of_eppa Gᶜ Hᶜ e hHalf
        (eppa_embedding_complement G H e hEppa) n hn φ')))
  · exact False.elim (NoHalfOrderEPPA.not_eppa_embedding
      (hOrthogonal.equalBipartitionThree.of_iso_or_compl hBipThree) G e hHalf hEppa)
  · exact False.elim (NoHalfOrderEPPA.not_eppa_embedding
      (noHalfOrderEPPA_of_bipartitionTen_model H hRank hBipFour) G e hHalf hEppa)
  · have hExcluded := orthogonalEight_model_excludes_forms hRank.2.2.1 hOrtho root
    exact False.elim ((hShape hOrtho).elim hExcluded.1 hExcluded.2)
  · exact Or.inr hOther

end EPPAIII.Primitive
