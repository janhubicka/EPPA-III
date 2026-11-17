import EPPAIII.Primitive.RookRecognition
import EPPAIII.Primitive.SchlaefliRecognition

/-! # The Schläfli row in the printed small rank-three catalogue -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open SimpleGraph

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
/-- The complement of the double-six model has the parameters in the
printed Schläfli row of Table 11.8. -/
theorem schlaefliModel_compl_isSRG : (schlaefliModelᶜ).IsSRGWith 27 10 1 5 := by
  constructor
  · decide
  · change ∀ v, (schlaefliModelᶜ).degree v = 10
    decide
  · decide
  · change ∀ v w, v ≠ w → ¬ (schlaefliModelᶜ).Adj v w →
      Fintype.card ((schlaefliModelᶜ).commonNeighbors v w) = 5
    decide

/-- The parameters of the printed Schläfli row identify the complement of the
concrete double-six graph. -/
theorem schlaefli_complement_iso_of_parameters {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hH : H.IsSRGWith 27 10 1 5) :
    Nonempty (H ≃g schlaefliModelᶜ) :=
  schlaefli_complement_unique H _ hH schlaefliModel_compl_isSRG

/-- The printed identities still needed after Schläfli, Clebsch and the
six rook models have been recognized. -/
def PublishedSmallRankThreeModelsExceptClebschSchlaefliAndRooks : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p : SRGParameters) (m : SmallConstituentHostModel) (complementModel : Bool),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentSourceModel p = some (m, complementModel) →
    m ≠ .foldedFiveCube → (∀ side, m ≠ .rook side false) → m ≠ .schlaefliComplement →
    Nonempty (H ≃g if complementModel then m.graphᶜ else m.graph)

/-- Add the proved Schläfli row to the remaining twelve printed identities. -/
theorem publishedSmallRankThreeModelsExceptClebschAndRooks_of_exceptSchlaefli
    (hSource : PublishedSmallRankThreeModelsExceptClebschSchlaefliAndRooks) :
    PublishedSmallRankThreeModelsExceptClebschAndRooks := by
  intro n H _ p m complementModel hPrim hRank hSRG hLabel hClebsch hRook
  by_cases hSchlaefli : m = .schlaefliComplement
  · subst m
    have hParameters : p = ⟨27, 10, 1, 5⟩ ∧ complementModel = false := by
      unfold smallConstituentSourceModel at hLabel
      split at hLabel <;> simp_all
    obtain ⟨rfl, rfl⟩ := hParameters
    exact schlaefli_complement_iso_of_parameters H hSRG
  · exact hSource H p m complementModel hPrim hRank hSRG hLabel hClebsch hRook hSchlaefli

end EPPAIII.Primitive
