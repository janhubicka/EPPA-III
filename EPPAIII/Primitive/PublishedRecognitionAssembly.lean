import EPPAIII.Primitive.GardinerFinRecognition
import EPPAIII.Primitive.PublishedLocalRecognition
import EPPAIII.Primitive.RookRecognition
import EPPAIII.Primitive.SmallRankThreeCodegrees
import EPPAIII.Primitive.SmallWitnessNamedClassification

/-! # The fixed-embedding classification from the published recognition data -/

namespace EPPAIII.Primitive

universe u v

/-- Source data for the recognition steps in the classification. The two
Table 11.8 inputs use the printed representatives; the parameters also
omit the adjacent codegree, which is forced by the SRG identity. -/
structure PublishedRecognitionSources : Prop where
  catalogue : FinPublishedRankThreeGraphCoverage
  gardiner : FinGardinerRecognition
  localRecognition : PublishedLocalRecognition.{v}
  smallParameters : PublishedSmallRankThreeNonadjacentCodegrees
  smallModels : PublishedSmallRankThreeModelsExceptClebschAndRooks

/-- Recover the recognition interface used inside the minimal-pair proof. -/
theorem PublishedRecognitionSources.to_primitiveRecognitionInputs
    (sources : PublishedRecognitionSources.{v}) : PrimitiveRecognitionInputs.{u, v} := by
  have exceptClebschAndRookFour :=
    publishedSmallRankThreeModelsExceptClebschAndRookFour_of_exceptClebschAndRooks sources.smallModels
  have exceptClebsch :=
    publishedSmallRankThreeModelsExceptClebsch_of_exceptClebschAndRookFour exceptClebschAndRookFour
  have printed := publishedSmallRankThreeModels_of_exceptClebsch exceptClebsch
  exact
    { gardinerSelected := fun G => gardinerRecognition_of_fin sources.gardiner G
      gardinerHost := fun hPositive H => gardinerRecognition_of_fin sources.gardiner H hPositive
      triangular := fun H => locallyTriangularRecognitionInputs_both_of_published sources.localRecognition H
      smallParameters := smallRankThreeParameterCoverage_of_publishedTable
        (publishedSmallRankThreeTable_of_nonadjacentCodegrees sources.smallParameters)
      smallModels := smallRankThreeModelIdentification_of_source
        (smallRankThreeSourceModelIdentification_of_published printed) }

/-- The named fixed-embedding classification with recognition specified
in terms of the published source data. Finite checks remain explicit. -/
theorem smallWitnessNamedModelCases_iff_eppa_of_published_sources
    (sources : PublishedRecognitionSources.{v})
    (hOrthogonal : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hFinite : PrimitiveFiniteChecks) (hTaylor : NamedTaylorFiniteChecks)
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H) :
    SmallWitnessNamedModelCases G H e ↔ IsEPPAEmbedding G H e :=
  smallWitnessNamedModelCases_iff_eppa (publishedRankThreeGraphCoverage_of_fin sources.catalogue)
    sources.to_primitiveRecognitionInputs hOrthogonal hPaley hFinite hTaylor G H e hInd hHalf hTrans

end EPPAIII.Primitive
