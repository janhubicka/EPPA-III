import EPPAIII.Primitive.RankThreeContextualCoverage
import EPPAIII.Primitive.PolarRankTwoArithmetic

/-! # Catalogue entries from the published rank-two parameters -/

namespace EPPAIII.Primitive

open SimpleGraph
attribute [local instance] Classical.propDecidable

/-- The SRG parameters and local clique chart of the point graph of a
rank-two polar geometry of order `(Q,t)`. -/
structure RankTwoPolarChart {n : ℕ} (H : SimpleGraph (Fin n)) (Q t : ℕ) : Prop where
  parameters : H.IsSRGWith ((Q + 1) * (Q * t + 1)) (Q * (t + 1)) (Q - 1) (t + 1)
  localCliques : ∀ r, Nonempty (localGraph H r ≃g cliqueUnion (t + 1) Q)

private theorem RankTwoPolarChart.catalogue_of_bound {n Q t k : ℕ}
    {H : SimpleGraph (Fin n)} (data : RankTwoPolarChart H Q t)
    (hRange : RankTwoPolarRange Q t) (hBound : k < (Q / 2).factorial ^ (t + 1))
    (hOrder : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤ k) :
    RankTwoPolarCatalogueModel H :=
  Or.inl ⟨Q, t, hRange, data.parameters, data.localCliques,
    fun r => (hOrder r).trans_lt hBound⟩

/-- The symplectic and odd orthogonal case at field order seven and above. -/
theorem rankTwoCatalogue_of_symplectic {n q f : ℕ} {H : SimpleGraph (Fin n)}
    (data : RankTwoPolarChart H q q)
    (hField : (q = 7 ∧ f = 1) ∨ (8 ≤ q ∧ f ≤ q))
    (hOrder : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤ f * q ^ 4 * (q - 1) * (q ^ 2 - 1)) :
    RankTwoPolarCatalogueModel H := by
  have hq : 4 ≤ q := by rcases hField with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  apply data.catalogue_of_bound (Or.inl ⟨hq, hq⟩) _ hOrder
  rcases hField with ⟨rfl, rfl⟩ | ⟨hq, hf⟩
  · simpa only [Nat.one_mul] using polar_rankTwo_seven_stabilizer_bounds.1
  · exact (polar_rankTwo_large_stabilizer_bounds q f hq hf).1

/-- The elliptic orthogonal case at field order seven and above. -/
theorem rankTwoCatalogue_of_elliptic {n q f : ℕ} {H : SimpleGraph (Fin n)}
    (data : RankTwoPolarChart H q (q ^ 2))
    (hField : (q = 7 ∧ f = 1) ∨ (8 ≤ q ∧ f ≤ q))
    (hOrder : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤
      2 * f * q ^ 6 * (q - 1) * (q ^ 4 - 1)) : RankTwoPolarCatalogueModel H := by
  have hq : 4 ≤ q := by rcases hField with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have ht : 4 ≤ q ^ 2 := (show 4 ≤ 4 ^ 2 by decide).trans (Nat.pow_le_pow_left hq 2)
  apply data.catalogue_of_bound (Or.inl ⟨hq, ht⟩) _ hOrder
  rcases hField with ⟨rfl, rfl⟩ | ⟨hq, hf⟩
  · simpa only [Nat.mul_one] using polar_rankTwo_seven_stabilizer_bounds.2
  · exact (polar_rankTwo_large_stabilizer_bounds q f hq hf).2.1

/-- The rank-two even unitary family at every field order at least three. -/
theorem rankTwoCatalogue_of_unitaryFour {n q f : ℕ} {H : SimpleGraph (Fin n)}
    (data : RankTwoPolarChart H (q ^ 2) q) (hq : 3 ≤ q) (hf : f ≤ q)
    (hOrder : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤ 2 * f * q ^ 6 * (q ^ 2 - 1) ^ 2) :
    RankTwoPolarCatalogueModel H :=
  data.catalogue_of_bound (Or.inr (Or.inl
    ⟨(show 5 ≤ 3 ^ 2 by decide).trans (Nat.pow_le_pow_left hq 2), hq⟩))
    (polar_rankTwo_unitary_stabilizer_bounds q f hq hf).1 hOrder

/-- The rank-two odd unitary family at every field order at least three. -/
theorem rankTwoCatalogue_of_unitaryFive {n q f : ℕ} {H : SimpleGraph (Fin n)}
    (data : RankTwoPolarChart H (q ^ 2) (q ^ 3)) (hq : 3 ≤ q) (hf : f ≤ q)
    (hOrder : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤
      2 * f * q ^ 10 * (q ^ 2 - 1) ^ 2 * (q ^ 3 + 1)) : RankTwoPolarCatalogueModel H :=
  data.catalogue_of_bound (Or.inr (Or.inl
    ⟨(show 5 ≤ 3 ^ 2 by decide).trans (Nat.pow_le_pow_left hq 2),
      (show 3 ≤ 3 ^ 3 by decide).trans (Nat.pow_le_pow_left hq 3)⟩))
    (polar_rankTwo_unitary_stabilizer_bounds q f hq hf).2 hOrder

/-- The line graph of the rank-two unitary geometry at every field order. -/
theorem rankTwoCatalogue_of_unitaryFiveDual {n q f : ℕ} {H : SimpleGraph (Fin n)}
    (data : RankTwoPolarChart H (q ^ 3) (q ^ 2)) (hq : 2 ≤ q) (hf : f ≤ q)
    (hOrder : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤
      2 * f * q ^ 10 * (q ^ 2 - 1) * (q ^ 4 - 1)) : RankTwoPolarCatalogueModel H :=
  data.catalogue_of_bound (Or.inl
    ⟨(show 4 ≤ 2 ^ 3 by decide).trans (Nat.pow_le_pow_left hq 3),
      Nat.pow_le_pow_left hq 2⟩)
    (unitaryFive_dual_stabilizer_bound q f hq hf) hOrder

end EPPAIII.Primitive
