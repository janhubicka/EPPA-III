import EPPAIII.BlockSystems.RookThreeFourSubsetOrbits

/-!
# R3 orbit arithmetic for nine outside vertices

For an arbitrary natural weight on the finite subsets of R3,
suppose the weight is invariant under the 72 genuine rook
automorphisms. The two-subset orbits have sizes 18,18, while
the three-subset orbits have sizes 6,6,36,36.

Thus no invariant nonnegative weight supported on subsets of
either fixed size 2 or fixed size 3 can sum to nine. This
formulates the numerical obstruction for Lemma 3.20
independently of EPPA; the latter supplies invariance of
the outside-neighbourhood multiplicities in a separate module.

Every orbit-disjointness fact is kernel-checked by Lean decide.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192

/-- A weight invariant under the indicated genuine subgroup
has the same value at every point of the representative orbit. -/
theorem rook_orbit_weight_sum
    (f : Finset rookVertex → ℕ)
    (hInvariant : ∀ S : Finset rookVertex, ∀ p : rookAutParameter,
      f (S.image (rookParameterizedAut p)) = f S)
    (S : Finset rookVertex) :
    (∑ T ∈ rookSubsetOrbit S, f T) =
      (rookSubsetOrbit S).card * f S := by
  classical
  calc
    (∑ T ∈ rookSubsetOrbit S, f T) =
        ∑ T ∈ rookSubsetOrbit S, f S := by
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hT
      exact hInvariant S p
    _ = (rookSubsetOrbit S).card * f S := by simp

theorem rook_pair_orbits_disjoint :
    Disjoint (rookSubsetOrbit rookTwoAdjacent)
      (rookSubsetOrbit rookTwoNonadjacent) := by
  decide

theorem rook_triple_orbits_disjoint :
    Disjoint (rookSubsetOrbit rookThreeClique)
      (rookSubsetOrbit rookThreeIndependent) ∧
    Disjoint
      (rookSubsetOrbit rookThreeClique ∪
        rookSubsetOrbit rookThreeIndependent)
      (rookSubsetOrbit rookThreeCorner) ∧
    Disjoint
      ((rookSubsetOrbit rookThreeClique ∪
        rookSubsetOrbit rookThreeIndependent) ∪
        rookSubsetOrbit rookThreeCorner)
      (rookSubsetOrbit rookThreeSingleEdge) := by
  decide

/-- Invariant multiplicities on the 36 pairs cannot total nine. -/
theorem rook_pair_weight_total_ne_nine
    (f : Finset rookVertex → ℕ)
    (hInvariant : ∀ S : Finset rookVertex, ∀ p : rookAutParameter,
      f (S.image (rookParameterizedAut p)) = f S)
    (hTotal :
      (∑ S ∈ (Finset.univ : Finset rookVertex).powersetCard 2, f S) = 9) :
    False := by
  have hExpanded :
      (∑ S ∈ (Finset.univ : Finset rookVertex).powersetCard 2, f S) =
        18 * f rookTwoAdjacent + 18 * f rookTwoNonadjacent := by
    rw [rook_two_subsets_orbit_partition,
      Finset.sum_union rook_pair_orbits_disjoint,
      rook_orbit_weight_sum f hInvariant rookTwoAdjacent,
      rook_orbit_weight_sum f hInvariant rookTwoNonadjacent,
      rookTwoAdjacent_orbit_card, rookTwoNonadjacent_orbit_card]
  rw [hExpanded] at hTotal
  omega

/-- Invariant multiplicities on the 84 triples cannot total nine:
every nonzero orbit contribution is divisible by six. -/
theorem rook_triple_weight_total_ne_nine
    (f : Finset rookVertex → ℕ)
    (hInvariant : ∀ S : Finset rookVertex, ∀ p : rookAutParameter,
      f (S.image (rookParameterizedAut p)) = f S)
    (hTotal :
      (∑ S ∈ (Finset.univ : Finset rookVertex).powersetCard 3, f S) = 9) :
    False := by
  obtain ⟨hAB,hABC,hABCD⟩ := rook_triple_orbits_disjoint
  have hExpanded :
      (∑ S ∈ (Finset.univ : Finset rookVertex).powersetCard 3, f S) =
        6 * f rookThreeClique + 6 * f rookThreeIndependent +
          36 * f rookThreeCorner + 36 * f rookThreeSingleEdge := by
    rw [rook_three_subsets_orbit_partition,
      Finset.sum_union hABCD, Finset.sum_union hABC,
      Finset.sum_union hAB,
      rook_orbit_weight_sum f hInvariant rookThreeClique,
      rook_orbit_weight_sum f hInvariant rookThreeIndependent,
      rook_orbit_weight_sum f hInvariant rookThreeCorner,
      rook_orbit_weight_sum f hInvariant rookThreeSingleEdge,
      rookThreeClique_orbit_card, rookThreeIndependent_orbit_card,
      rookThreeCorner_orbit_card, rookThreeSingleEdge_orbit_card]
  rw [hExpanded] at hTotal
  omega

end EPPAIII.BlockSystems
