import EPPAIII.Primitive.SchlaefliSourceModel
import EPPAIII.Primitive.SmallConstituentExclusion
import EPPAIII.Primitive.SmallPaleyRecognition
import EPPAIII.Primitive.TriangularActionRecognition

/-! # Source data for the screened rank-three graph identifications -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

/-- The three remaining direct model identifications from Table 11.8. -/
def PublishedSmallOrthogonalModels : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p : SRGParameters) (m : SmallConstituentHostModel) (complementModel : Bool),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentSourceModel p = some (m, complementModel) →
    m.IsOrthogonalSearchCase → Nonempty (H ≃g if complementModel then m.graphᶜ else m.graph)

/-- Published permutation data and direct graph identities for the
screened rows whose models are not reconstructed from graph parameters. -/
structure PublishedSmallModelSources : Prop where
  triangular : PublishedSmallTriangularActions
  paley : PublishedSmallPaleyActionSources
  orthogonal : PublishedSmallOrthogonalModels

private theorem PublishedSmallPaleyActionSources.prime_model_of_row
    (sources : PublishedSmallPaleyActionSources) {n q : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (p : SRGParameters) (other : Bool)
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H)
    (hSRG : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hRow : smallConstituentSourceModel p = some (.paleyPrime q, other)) :
    Nonempty (H ≃g if other then (paleyPrimeModel q)ᶜ else paleyPrimeModel q) := by
  have hCases :
      (p = ⟨17, 8, 3, 4⟩ ∧ q = 17 ∧ other = false) ∨
      (p = ⟨37, 18, 8, 9⟩ ∧ q = 37 ∧ other = false) ∨
      (p = ⟨41, 20, 9, 10⟩ ∧ q = 41 ∧ other = false) := by
    unfold smallConstituentSourceModel at hRow
    split at hRow <;> simp_all
  rcases hCases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hn : n = 17 := by simpa using hSRG.card
    subst n
    exact sources.seventeen_model H hPrim hRank hSRG
  · have hn : n = 37 := by simpa using hSRG.card
    subst n
    exact sources.thirtySeven_model H hPrim hRank hSRG
  · have hn : n = 41 := by simpa using hSRG.card
    subst n
    exact sources.fortyOne_model H hPrim hRank hSRG

private theorem PublishedSmallPaleyActionSources.twentyFive_model_of_row
    (sources : PublishedSmallPaleyActionSources) {n : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (p : SRGParameters) (other : Bool)
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H)
    (hSRG : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hRow : smallConstituentSourceModel p = some (.paleyTwentyFive, other)) :
    Nonempty (H ≃g if other then paleyTwentyFiveModelᶜ else paleyTwentyFiveModel) := by
  have hParams : p = ⟨25, 12, 5, 6⟩ ∧ other = false := by
    unfold smallConstituentSourceModel at hRow
    split at hRow <;> simp_all
  obtain ⟨rfl, rfl⟩ := hParams
  have hn : n = 25 := by simpa using hSRG.card
  subst n
  exact sources.twentyFive_model H hPrim hRank hSRG

private theorem PublishedSmallModelSources.remaining_models (sources : PublishedSmallModelSources) :
    PublishedSmallRankThreeModelsExceptClebschSchlaefliAndRooks := by
  intro n H _ p m other hPrim hRank hSRG hRow hClebsch hRook hSchlaefli
  cases m with
  | rook side complemented =>
      cases complemented
      · exact (hRook side rfl).elim
      · unfold smallConstituentSourceModel at hRow
        split at hRow <;> simp_all
  | triangularComplement side =>
      exact sources.triangular.source_model H p hPrim hRank hSRG hRow
  | paleyPrime q => exact sources.paley.prime_model_of_row H p other hPrim hRank hSRG hRow
  | paleyTwentyFive => exact sources.paley.twentyFive_model_of_row H p other hPrim hRank hSRG hRow
  | foldedFiveCube => exact (hClebsch rfl).elim
  | schlaefliComplement => exact (hSchlaefli rfl).elim
  | equalBipartitionEight =>
      exact sources.orthogonal H p _ other hPrim hRank hSRG hRow (Or.inl rfl)
  | orthogonalSixMinus =>
      exact sources.orthogonal H p _ other hPrim hRank hSRG hRow (Or.inr (Or.inl rfl))
  | affineOrthogonalSixMinusComplement =>
      exact sources.orthogonal H p _ other hPrim hRank hSRG hRow (Or.inr (Or.inr rfl))

/-- Supply all the printed model identities to the small-constituent screen. -/
theorem PublishedSmallModelSources.to_printedModels (sources : PublishedSmallModelSources) :
    PublishedSmallRankThreeModels := by
  apply publishedSmallRankThreeModels_of_exceptClebsch
  apply publishedSmallRankThreeModelsExceptClebsch_of_exceptClebschAndRookFour
  apply publishedSmallRankThreeModelsExceptClebschAndRookFour_of_exceptClebschAndRooks
  apply publishedSmallRankThreeModelsExceptClebschAndRooks_of_exceptSchlaefli
  exact sources.remaining_models

end EPPAIII.Primitive
