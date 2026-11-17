import EPPAIII.Primitive.AffineStabilizerRecognition
import EPPAIII.Primitive.RankThreeFamilyReductions

/-! # Source adapters for the finite affine stabilizer rows -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open SimpleGraph

attribute [local instance] Classical.propDecidable

/-- A single full point-stabilizer bound suffices for any of the four
published conference rows. -/
theorem RecognizedRankThreeFamily.affineConference_of_singleton_bound
    {n : ℕ} {H : SimpleGraph (Fin n)} (row : AffineConferenceRow)
    (hSRG : let p := row.parameters; H.IsSRGWith p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hRank : HasRankThreeAutAction H) (r : Fin n)
    (hPoint : Nat.card (hostPointwiseStabilizer H {r}) ≤ row.pointBound) :
    RecognizedRankThreeFamily H :=
  .affineConference row hSRG hRank fun x =>
    (card_hostPointwiseStabilizer_singleton_of_transitive H hRank.2.2.1 x r).trans_le hPoint

/-- The published full graph group order also gives the conference input,
without the order of any separately supplied point or pair stabilizer. -/
theorem RecognizedRankThreeFamily.affineConference_of_full_order_bound
    {n : ℕ} {H : SimpleGraph (Fin n)} (row : AffineConferenceRow)
    (hSRG : let p := row.parameters; H.IsSRGWith p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hRank : HasRankThreeAutAction H)
    (hOrder : Nat.card (graphAutomorphisms H) ≤ n * row.pointBound) :
    RecognizedRankThreeFamily H :=
  .affineConference row hSRG hRank fun x =>
    card_hostPointwiseStabilizer_singleton_le_of_full_order H hRank.2.2.1 x
      (by simpa only [Nat.card_fin] using hOrder)

/-- The possible point-stabilizer orders from the full graph groups listed by
Brouwer and Van Maldeghem in Sections 10.18, 10.30, 10.70, and 10.86.
Repeated orders are listed once. -/
def AffineConferenceRow.publishedPointOrders : AffineConferenceRow → List ℕ
  | .order49 => [48, 72]
  | .order81 => [160, 480]
  | .order529 => [528, 264]
  | .order2209 => [1104, 2208]

/-- An exact full group order from the relevant source row gives the
conference input. The order equality is the external model datum. -/
theorem RecognizedRankThreeFamily.affineConference_of_published_full_order
    {n : ℕ} {H : SimpleGraph (Fin n)} (row : AffineConferenceRow)
    (hSRG : let p := row.parameters; H.IsSRGWith p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hRank : HasRankThreeAutAction H) {b : ℕ} (hb : b ∈ row.publishedPointOrders)
    (hOrder : Nat.card (graphAutomorphisms H) = n * b) : RecognizedRankThreeFamily H := by
  have hBound : b ≤ row.pointBound := by
    cases row <;> simp [AffineConferenceRow.publishedPointOrders] at hb <;>
      rcases hb with rfl | rfl <;> decide
  exact .affineConference_of_full_order_bound row hSRG hRank
    (hOrder.le.trans (Nat.mul_le_mul_left n hBound))

/-- A full automorphism order bound for a rank-three SRG gives the affine
two-anchor catalogue input from the two subdegrees. -/
theorem RecognizedRankThreeFamily.affinePairBound_of_full_order_bound
    {n k l μ d b : ℕ} {H : SimpleGraph (Fin n)} (hSRG : H.IsSRGWith n k l μ)
    (hRank : HasRankThreeAutAction H) (hd : 0 < d) (hEdge : d ≤ k)
    (hNonedge : d ≤ n - k - 1) (hSize : 8 * b + 4 < n)
    (hOrder : Nat.card (graphAutomorphisms H) ≤ n * (d * b)) :
    RecognizedRankThreeFamily H :=
  .affinePairBound hSize fun x y hxy =>
    hostPairStabilizer_le_of_srg_and_singleton_bound H hRank hSRG hd hEdge hNonedge x
      (card_hostPointwiseStabilizer_singleton_le_of_full_order H hRank.2.2.1 x
        (by simpa only [Nat.card_fin] using hOrder)) x y hxy

/-- The 81-vertex three-anchor input follows from the two subdegrees forty
and the published upper bound 480 on the full point stabilizer. -/
theorem RecognizedRankThreeFamily.affineEightyOne_of_full_order_bound
    {H : SimpleGraph (Fin 81)} (hSRG : H.IsSRGWith 81 40 19 20)
    (hRank : HasRankThreeAutAction H)
    (hOrder : Nat.card (graphAutomorphisms H) ≤ 81 * 480) :
    RecognizedRankThreeFamily H :=
  .affineEightyOne rfl fun x y hxy =>
    hostPairStabilizer_le_of_srg_and_singleton_bound H hRank hSRG
      (d := 40) (by decide) (by decide) (by decide) x
      (card_hostPointwiseStabilizer_singleton_le_of_full_order H hRank.2.2.1 x
        (by simpa only [Nat.card_fin] using hOrder)) x y hxy

end EPPAIII.Primitive
