import EPPAIII.Primitive.LocallyTriangularFaithful
import EPPAIII.Primitive.TriangularConstituentReduction

/-! # Published recognition of connected locally triangular and Kneser graphs -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

universe v

/-- The source classifications for connected graphs. The triangular
classification is restricted to the strongly regular case. The Mathieu
point bound is needed at one root. The order-256 point bound is derived
from local triangularity and the strongly regular parameters. -/
structure PublishedLocalRecognition : Prop where
  triangular : ∀ {W : Type v} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (k l μ : ℕ), H.Connected → H ≠ ⊤ →
    H.IsSRGWith (Fintype.card W) k l μ →
    ∀ m, 5 ≤ m → UniformLocalModel H (triangularModel m) →
      Nonempty (H ≃g clebschGraphᶜ) ∨
      Nonempty (H ≃g (vectorOrthogonalSixGraph true)ᶜ) ∨
      (m = 10 ∧ Fintype.card W = 256) ∨ (m = 24 ∧ Fintype.card W = 2048)
  golayPoint : ∀ {W : Type v} [Fintype W] (H : SimpleGraph W),
    H.Connected → HasRankThreeAutAction H → Fintype.card W = 2048 →
    UniformLocalModel H (triangularModel 24) →
      ∃ r, Nat.card (hostPointwiseStabilizer H {r}) ≤ 244823040
  kneserFive : ∀ {W : Type v} [Fintype W] (H : SimpleGraph W), H.Connected →
    UniformLocalModel H (triangularModel 5)ᶜ →
      Nonempty (H ≃g (triangularModel 7)ᶜ) ∨ Fintype.card W = 63 ∨ Fintype.card W = 65
  kneserSix : ∀ {W : Type v} [Fintype W] (H : SimpleGraph W), H.Connected →
    UniformLocalModel H (triangularModel 6)ᶜ →
      Nonempty (H ≃g (triangularModel 8)ᶜ) ∨ Fintype.card W = 32 ∨
        Nonempty (H ≃g orthogonalSixGraph false false)
  kneserLarge : ∀ {W : Type v} [Fintype W] (H : SimpleGraph W), H.Connected →
    ∀ m, 7 ≤ m → UniformLocalModel H (triangularModel m)ᶜ →
      Nonempty (H ≃g (triangularModel (m + 2))ᶜ)

private instance triangularAdj (m : ℕ) : DecidableRel (triangularModel m).Adj := by
  intro a b
  change Decidable (a ≠ b ∧ ∃ x : Fin m, x ∈ a.val ∧ x ∈ b.val)
  infer_instance

private def tenPair : TriangularVertex 10 := triangularPair 0 1 (by decide)

private theorem tenPair_degree : (triangularModel 10).degree tenPair = 16 := by decide

/-- The locally triangular rank-three graph of order 256 has point
stabilizers bounded by `10!` from graph data alone. -/
theorem locallyTriangular_ten_point_bound {W : Type*} [Fintype W] (H : SimpleGraph W)
    (hRank : HasRankThreeAutAction H) (hCard : Fintype.card W = 256)
    (hLocal : UniformLocalModel H (triangularModel 10)) (r : W) :
    Nat.card (hostPointwiseStabilizer H {r}) ≤ 3628800 := by
  classical
  obtain ⟨k, l, μ, hSRG⟩ := rankThree_isSRG H hRank
  obtain ⟨kEq, lEq⟩ := srg_parameters_of_rooted_local_iso H (triangularModel 10)
    hSRG r (hLocal r).some.symm tenPair
  have hk : k = 45 := by
    have hSize : Fintype.card (TriangularVertex 10) = 45 := by
      rw [triangularGraph_card, Fintype.card_fin]
      decide
    exact kEq.trans hSize
  have hl : l = 16 := lEq.trans tenPair_degree
  have hPos : 0 < Fintype.card W := by omega
  have hEq := hSRG.param_eq H hPos
  rw [hk, hl, hCard] at hEq
  have hμ : μ = 6 := by omega
  subst μ
  have hWidth : 5 ≤ Fintype.card (Fin 10) := by decide
  exact locallyTriangular_hostPointwiseStabilizer_card_le H hSRG hWidth hLocal r

/-- Apply the source classifications to any connected rank-three host. -/
theorem locallyTriangularRecognitionInputs_of_connected
    (hPublished : PublishedLocalRecognition.{v})
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (hConn : H.Connected) (hRank : HasRankThreeAutAction H) :
    LocallyTriangularRecognitionInputs H := by
  classical
  refine ⟨?_, hPublished.kneserFive H hConn, hPublished.kneserSix H hConn,
    hPublished.kneserLarge H hConn⟩
  intro m hm hLocal
  obtain ⟨k, l, μ, hSRG⟩ := rankThree_isSRG H hRank
  have hIncomplete : H ≠ ⊤ := by
    obtain ⟨a, b, hab, hn⟩ := hRank.2.1
    intro hTop
    exact hn (hTop.symm ▸ (show (⊤ : SimpleGraph W).Adj a b from hab))
  rcases hPublished.triangular H k l μ hConn hIncomplete hSRG m hm hLocal with hC | hF | hTen | hGolay
  · exact Or.inl hC
  · exact Or.inr (Or.inl hF)
  · obtain ⟨rfl, hCard⟩ := hTen
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hCard,
      locallyTriangular_ten_point_bound H hRank hCard hLocal⟩))
  · obtain ⟨rfl, hCard⟩ := hGolay
    obtain ⟨r, hr⟩ := hPublished.golayPoint H hConn hRank hCard hLocal
    refine Or.inr (Or.inr (Or.inr ⟨rfl, hCard, fun s => ?_⟩))
    rw [← card_hostPointwiseStabilizer_singleton_of_transitive H hRank.2.2.1 r s]
    exact hr

/-- Both recognition orientations follow from the same published facts,
since an invariant equivalence would disconnect a primitive rank-three
graph or its complement. -/
theorem locallyTriangularRecognitionInputs_both_of_published
    (hPublished : PublishedLocalRecognition.{v})
    {W : Type v} [Fintype W] (H : SimpleGraph W)
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H) :
    LocallyTriangularRecognitionInputs H ∧ LocallyTriangularRecognitionInputs Hᶜ := by
  obtain ⟨hConn, hConnC⟩ := primitive_rankThree_connected H hPrim hRank
  exact ⟨locallyTriangularRecognitionInputs_of_connected hPublished H hConn hRank,
    locallyTriangularRecognitionInputs_of_connected hPublished Hᶜ hConnC (complement_rankThree hRank)⟩

end EPPAIII.Primitive
