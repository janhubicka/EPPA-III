import EPPAIII.Primitive.RankThreeFamilyReductions
import EPPAIII.Primitive.SporadicStabilizerRecognition

/-! # Sporadic rows from full group orders and one constituent chart -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems EPPAIII.CliqueCovers

attribute [local instance] Classical.propDecidable

/-- Recognize the Gewirtz row from the full group order. -/
theorem RecognizedRankThreeFamily.gewirtz_of_full_order
    {n : ℕ} {H : SimpleGraph (Fin n)}
    (hSRG : H.IsSRGWith 56 10 0 2) (hRank : HasRankThreeAutAction H)
    (hOrder : Nat.card (graphAutomorphisms H) = 80640) :
    RecognizedRankThreeFamily H :=
  .gewirtz hSRG (gewirtz_nonedge_stabilizer_card_of_full_order H hSRG hRank hOrder)

/-- Recognize the M₂₂ row from the full group order. -/
theorem RecognizedRankThreeFamily.mathieuTwentyTwo_of_full_order
    {n : ℕ} {H : SimpleGraph (Fin n)}
    (hSRG : H.IsSRGWith 77 16 0 4) (hRank : HasRankThreeAutAction H)
    (hOrder : Nat.card (graphAutomorphisms H) = 887040) :
    RecognizedRankThreeFamily H :=
  .mathieuTwentyTwo hSRG hRank
    (mathieuTwentyTwo_point_stabilizer_card_of_full_order H hSRG hRank hOrder)

/-- Recognize the Higman–Sims row using one chart and the full group order
of its M₂₂ constituent. -/
theorem RecognizedRankThreeFamily.higmanSims_of_one_model
    {n : ℕ} {X : Type} [Fintype X] {H : SimpleGraph (Fin n)}
    (hSRG : H.IsSRGWith 100 22 0 6) (hTrans : HasTransitiveGraphAutomorphisms H)
    (M : SimpleGraph X) (hMSRG : M.IsSRGWith 77 16 0 4)
    (hMRank : HasRankThreeAutAction M) (hMGroup : Nat.card (graphAutomorphisms M) = 887040)
    (r : Fin n) (φ : nonlocalGraph H r ≃g M) :
    RecognizedRankThreeFamily H := by
  obtain ⟨hMStabilizer, hModel, hStabilizer⟩ :=
    higmanSims_catalogue_data_of_one_model H hSRG hTrans M hMSRG hMRank hMGroup r φ
  exact .higmanSims hSRG M hMSRG hMRank hMStabilizer hModel hStabilizer

end EPPAIII.Primitive
