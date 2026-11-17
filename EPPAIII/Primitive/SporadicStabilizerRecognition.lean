import EPPAIII.Primitive.AffineMatchingExclusion
import EPPAIII.Primitive.AffineStabilizerRecognition
import EPPAIII.Primitive.TriangleFreeNonlocalAction

/-! # Recovering sporadic stabilizer data from full group orders -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems EPPAIII.CliqueCovers

/-- The Gewirtz rank-three action has nonedge subdegree 45, so its full
automorphism group order gives every nonedge stabilizer order. -/
theorem gewirtz_nonedge_stabilizer_card_of_full_order {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hSRG : H.IsSRGWith 56 10 0 2)
    (hRank : HasRankThreeAutAction H) (hAuto : Nat.card (graphAutomorphisms H) = 80640)
    (r s : W) (hrs : r ≠ s) (hNonedge : ¬ H.Adj r s) :
    Nat.card (pointwiseGraphStabilizer H {r, s}) = 32 := by
  classical
  have hPoint := card_pointwiseGraphStabilizer_singleton_of_full_order H hRank.2.2.1 r
    (b := 1440) (by simpa only [Nat.card_eq_fintype_card, hSRG.card] using hAuto)
  have hPair := pointwiseGraphStabilizer_card_mul_srg_subdegree H hRank hSRG r s hrs
  rw [ite_eq_right hNonedge, hPoint] at hPair
  change Nat.card (pointwiseGraphStabilizer H {r, s}) * 45 = 1440 at hPair
  omega

/-- The full automorphism group order of the M₂₂ graph determines every
point stabilizer order by vertex transitivity. -/
theorem mathieuTwentyTwo_point_stabilizer_card_of_full_order {W : Type*} [Fintype W]
    (M : SimpleGraph W) [DecidableRel M.Adj] (hSRG : M.IsSRGWith 77 16 0 4)
    (hRank : HasRankThreeAutAction M) (hAuto : Nat.card (graphAutomorphisms M) = 887040)
    (r : W) : Nat.card (pointwiseGraphStabilizer M {r}) = 11520 :=
  card_pointwiseGraphStabilizer_singleton_of_full_order M hRank.2.2.1 r
    (by simpa only [Nat.card_eq_fintype_card, hSRG.card] using hAuto)

/-- Vertex transitivity transports a single Higman–Sims constituent model
to every root. The faithful action on each constituent bounds the order
of every Higman–Sims point stabilizer. -/
theorem higmanSims_catalogue_data_of_one_model {W X : Type*} [Fintype W] [Fintype X]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hSRG : H.IsSRGWith 100 22 0 6)
    (hTrans : HasTransitiveGraphAutomorphisms H)
    (M : SimpleGraph X) [DecidableRel M.Adj] (hMSRG : M.IsSRGWith 77 16 0 4)
    (hMRank : HasRankThreeAutAction M) (hMGroup : Nat.card (graphAutomorphisms M) = 887040)
    (r : W) (φ : nonlocalGraph H r ≃g M) :
    (∀ s : X, Nat.card (pointwiseGraphStabilizer M {s}) = 11520) ∧
      (∀ s : W, Nonempty (nonlocalGraph H s ≃g M)) ∧
      (∀ s : W, Nat.card (pointwiseGraphStabilizer H {s}) ≤ 887040) := by
  have hModel (s : W) : Nonempty (nonlocalGraph H s ≃g M) := by
    obtain ⟨q, hq, hMove⟩ := hTrans r s
    let a : H ≃g H := ⟨q, fun {x y} => (hq x y).symm⟩
    change a r = s at hMove
    rw [← hMove]
    exact ⟨(nonlocalIso a r).symm.trans φ⟩
  refine ⟨mathieuTwentyTwo_point_stabilizer_card_of_full_order M hMSRG hMRank hMGroup,
    hModel, ?_⟩
  intro s
  obtain ⟨ψ⟩ := hModel s
  exact (card_pointwiseGraphStabilizer_singleton_le_nonlocalAutomorphisms H hSRG
    (by decide) s).trans_eq ((card_automorphisms_of_iso ψ).trans hMGroup)

end EPPAIII.Primitive
