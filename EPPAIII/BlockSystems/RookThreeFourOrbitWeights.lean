import EPPAIII.BlockSystems.RookThreeOrbitWeights

/-!
# R3 invariant weights on four-element subsets

The five size-four subset orbits of the rook graph have sizes
9,9,36,36,36. Hence an invariant nonnegative multiplicity
function of total weight nine must assign multiplicity one to
exactly one of the two size-nine orbits and zero to all others.

The finite orbit-disjointness certificates are verified by
kernel computation, while the weight identity follows from
the general orbit-sum lemma and elementary natural arithmetic.
This is the abstract counting step for cross-degree four
in Lemma 3.20.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192

theorem rook_four_orbits_disjoint :
    Disjoint (rookSubsetOrbit rookFourSquare)
      (rookSubsetOrbit rookFourNineOther) ∧
    Disjoint
      (rookSubsetOrbit rookFourSquare ∪
        rookSubsetOrbit rookFourNineOther)
      (rookSubsetOrbit rookFourLinePlus) ∧
    Disjoint
      ((rookSubsetOrbit rookFourSquare ∪
        rookSubsetOrbit rookFourNineOther) ∪
        rookSubsetOrbit rookFourLinePlus)
      (rookSubsetOrbit rookFourCornerPlus) ∧
    Disjoint
      (((rookSubsetOrbit rookFourSquare ∪
        rookSubsetOrbit rookFourNineOther) ∪
        rookSubsetOrbit rookFourLinePlus) ∪
        rookSubsetOrbit rookFourCornerPlus)
      (rookSubsetOrbit rookFourCornerDiagonal) := by
  decide

/-- Exactly one of the two size-nine profile orbits can occur
when the total invariant multiplicity is nine. -/
theorem rook_four_weight_total_nine_classification
    (f : Finset rookVertex → ℕ)
    (hInvariant : ∀ S : Finset rookVertex, ∀ p : rookAutParameter,
      f (S.image (rookParameterizedAut p)) = f S)
    (hTotal :
      (∑ S ∈ (Finset.univ : Finset rookVertex).powersetCard 4, f S) = 9) :
    f rookFourSquare + f rookFourNineOther = 1 ∧
    f rookFourLinePlus = 0 ∧
    f rookFourCornerPlus = 0 ∧
    f rookFourCornerDiagonal = 0 := by
  obtain ⟨hAB,hABC,hABCD,hABCDE⟩ := rook_four_orbits_disjoint
  have hExpanded :
      (∑ S ∈ (Finset.univ : Finset rookVertex).powersetCard 4, f S) =
        9 * f rookFourSquare + 9 * f rookFourNineOther +
        36 * f rookFourLinePlus + 36 * f rookFourCornerPlus +
        36 * f rookFourCornerDiagonal := by
    rw [rook_four_subsets_orbit_partition,
      Finset.sum_union hABCDE, Finset.sum_union hABCD,
      Finset.sum_union hABC, Finset.sum_union hAB,
      rook_orbit_weight_sum f hInvariant rookFourSquare,
      rook_orbit_weight_sum f hInvariant rookFourNineOther,
      rook_orbit_weight_sum f hInvariant rookFourLinePlus,
      rook_orbit_weight_sum f hInvariant rookFourCornerPlus,
      rook_orbit_weight_sum f hInvariant rookFourCornerDiagonal,
      rookFourSquare_orbit_card, rookFourNineOther_orbit_card,
      rookFourLinePlus_orbit_card, rookFourCornerPlus_orbit_card,
      rookFourCornerDiagonal_orbit_card]
  rw [hExpanded] at hTotal
  omega

end EPPAIII.BlockSystems
