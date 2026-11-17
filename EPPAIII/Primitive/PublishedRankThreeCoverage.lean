import EPPAIII.Primitive.PrimitiveClassificationReduction
import EPPAIII.Primitive.SmallRankThreeParameterRecognition

/-!
# Graph recognition input for the primitive classification

The cited rank-three classification supplies the list of graph families. This
interface also asks for the independent geometric and full-automorphism data
used by the corresponding reduction. The hypotheses of graph recognition do
not refer to an EPPA selection.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

universe u v

/-- A graph on the published list with the model data required for its reduction.
The first five entries are fixed constructions. The remaining entries carry
only graph and action data, independent of the EPPA pair. -/
def HasPublishedRankThreeModel {W : Type*} (H : SimpleGraph W) : Prop :=
  (∃ n ≥ 3, IsModelUpToComplement H (rookGraph n)) ∨
  (∃ n ≥ 5, IsModelUpToComplement H (triangularModel n)) ∨
  IsModelUpToComplement H (equalBipartitionGraph 3) ∨
  IsModelUpToComplement H (equalBipartitionGraph 4) ∨
  IsModelUpToComplement H nonsingularOrthogonalEightGraph ∨
  (∃ model : FiniteGraphModel, CompleteRankThreeCase model.2 ∧
    IsModelUpToComplement H model.2)

/-- The graph-level projection of the published classification together
with independently supplied model recognition. -/
def PublishedRankThreeGraphCoverage : Prop :=
  ∀ {W : Type v} [Fintype W] (H : SimpleGraph W),
    IsPrimitiveAutAction H → HasRankThreeAutAction H → HasPublishedRankThreeModel H

/-- The graph-level catalogue can be supplied on standard vertex sets.
The model-specific graph and action data are still part of the conclusion. -/
def FinPublishedRankThreeGraphCoverage : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)),
    IsPrimitiveAutAction H → HasRankThreeAutAction H → HasPublishedRankThreeModel H

theorem HasPublishedRankThreeModel.of_iso {A B : Type*}
    {G : SimpleGraph A} {H : SimpleGraph B} (hModel : HasPublishedRankThreeModel G)
    (φ : G ≃g H) : HasPublishedRankThreeModel H := by
  have lift {C : Type*} {J : SimpleGraph C} (h : IsModelUpToComplement G J) :
      IsModelUpToComplement H J := by
    rcases h with ⟨e⟩ | ⟨e⟩
    · exact Or.inl ⟨φ.symm.trans e⟩
    · exact Or.inr ⟨φ.symm.trans e⟩
  rcases hModel with ⟨n, hn, h⟩ | ⟨n, hn, h⟩ | h | h | h | ⟨K, hK, h⟩
  · exact Or.inl ⟨n, hn, lift h⟩
  · exact Or.inr (Or.inl ⟨n, hn, lift h⟩)
  · exact Or.inr (Or.inr (Or.inl (lift h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (lift h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (lift h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨K, hK, lift h⟩))))

/-- Relabel an arbitrary finite host before applying the published catalogue. -/
theorem publishedRankThreeGraphCoverage_of_fin (hFin : FinPublishedRankThreeGraphCoverage) :
    PublishedRankThreeGraphCoverage.{v} := by
  intro W _ H hPrim hRank
  let labels := (Fintype.equivFin W).symm
  let φ : pullbackGraph H labels ≃g H := ⟨labels, Iff.rfl⟩
  exact (hFin _ (primitive_pullback_equiv H labels hPrim)
    (rankThree_pullback H labels hRank)).of_iso φ

private def coveredModels : RankThreeCatalog := fun _ => {model | CompleteRankThreeCase model.2}

/-- Family labels organize the external catalogue. Once a recognized model
is supplied for each host, its label is immaterial to the reduction. -/
theorem publishedRankThreeGraphCoverage_iff_catalogue :
    PublishedRankThreeGraphCoverage.{v} ↔
      ∃ catalogue : RankThreeCatalog, RankThreeClassification.{v} catalogue ∧
        (∀ c K, K ∈ catalogue c → CompleteRankThreeCase K.2) := by
  have move {W : Type v} (H : SimpleGraph W) :
      HasPublishedRankThreeModel H → InRankThreeCatalog coveredModels H := by
    unfold HasPublishedRankThreeModel InRankThreeCatalog
    exact Or.imp id (Or.imp id (Or.imp id (Or.imp id
      (Or.imp id (fun ⟨model, hData, hIso⟩ =>
        ⟨RankThreeExternalCase.classicalIndividualModels, model, hData, hIso⟩)))))
  constructor
  · intro h
    refine ⟨coveredModels, ?_, fun _ _ hData => hData⟩
    intro W _ H hPrim hRank
    exact move H (h H hPrim hRank)
  · rintro ⟨catalogue, hCatalogue, hData⟩ W _ H hPrim hRank
    have h := hCatalogue H hPrim hRank
    unfold InRankThreeCatalog at h
    unfold HasPublishedRankThreeModel
    exact Or.imp id (Or.imp id (Or.imp id (Or.imp id
      (Or.imp id (fun ⟨c, model, hMem, hIso⟩ => ⟨model, hData c model hMem, hIso⟩))))) h

/-- Primitive EPPA classification for an actual selected embedding.
The graph recognition, local recognition, and finite inputs are explicit. -/
theorem primitiveCases_iff_eppa_of_publishedRankThreeCoverage
    (hPublished : PublishedRankThreeGraphCoverage.{v})
    (hRecognize : PrimitiveRecognitionInputs.{u, v})
    (hSearch : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hFinite : PrimitiveFiniteChecks)
    {V : Type u} {W : Type v} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPrim : IsPrimitiveAutAction H) :
    primitiveCases G H e ↔ IsEPPAEmbedding G H e := by
  obtain ⟨catalogue, hCatalogue, hData⟩ := publishedRankThreeGraphCoverage_iff_catalogue.mp hPublished
  exact primitiveCases_iff_eppa_of_catalogue catalogue hCatalogue hData
    hRecognize hSearch hPaley hFinite G H e hInd hHalf hTrans hPrim

end EPPAIII.Primitive
