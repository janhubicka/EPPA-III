import EPPAIII.BlockSystems.CycleFivePairProfileOrbits
import EPPAIII.BlockSystems.RookThreeProfileSum
import EPPAIII.BlockSystems.OutsideProfileCanonicalIndexing

/-!
# Saturating the five outside pair profiles of an EPPA witness for C5

An actual ten-vertex EPPA witness for the five-cycle has precisely five
outside vertices. Suppose each outside vertex has two neighbours in
the distinguished C5. The five cyclic shifts of either pair-profile
form a whole orbit, and EPPA makes its multiplicity constant.

The two disjoint orbits of pairs both have size five. Since all
outside-profile multiplicities together sum to five, precisely one
orbit has multiplicity one and the other orbit has multiplicity zero.

Therefore the actual outside profiles consist of exactly the five
adjacent pairs, or exactly the five nonadjacent pairs, each appearing
once. The outside half is canonically labelled by these profiles,
so in particular a C4 ⊔ C6 disconnected bipartite cross pattern is
impossible. No separate transitivity assumption on the host and no
a priori outside labelling or coherent EPPA lifts are required.
-/

namespace EPPAIII.BlockSystems

/-- Orbit-invariant weights have constant value on each cyclic orbit. -/
theorem cycleFive_orbit_weight_sum
    (f : Finset (Fin 5) → ℕ)
    (hInv : ∀ S : Finset (Fin 5), ∀ d : Fin 5,
      f (S.image (Equiv.addRight d)) = f S)
    (S : Finset (Fin 5)) :
    (∑ T ∈ cycleFiveSubsetOrbit S, f T) =
      (cycleFiveSubsetOrbit S).card * f S := by
  classical
  calc
    (∑ T ∈ cycleFiveSubsetOrbit S, f T) =
        ∑ T ∈ cycleFiveSubsetOrbit S, f S := by
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hT
      rw [← hd]
      exact hInv S d
    _ = (cycleFiveSubsetOrbit S).card * f S := by simp

/-- For every C5 outside vertex of cross-degree two, its profile is
one of the two pair orbits and the outside profiles collectively
realise exactly one full orbit with multiplicity one. -/
theorem cycleFive_eppa_outside_pair_profile_classification
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 2) :
    ((finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        cycleFiveSubsetOrbit cycleFiveEdgePair ∨
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        cycleFiveSubsetOrbit cycleFiveDiagonalPair) ∧
      Set.InjOn (finiteNeighbourhoodProfile H e)
        (finiteOutside e : Set W) := by
  classical
  let f : Finset (Fin 5) → ℕ :=
    outsideProfileMultiplicity H e
  have hOutsideCard : (finiteOutside e).card = 5 := by
    have h := finiteOutside_card e
    have hBase : Fintype.card (Fin 5) = 5 := by decide
    omega
  have hInv : ∀ S : Finset (Fin 5), ∀ d : Fin 5,
      f (S.image (Equiv.addRight d)) = f S := by
    intro S d
    exact cycleFive_outside_profile_multiplicity_invariant
      H e heppa S d
  have hTotal :
      (∑ S ∈ (Finset.univ : Finset (Fin 5)).powersetCard 2, f S) = 5 := by
    have hSum := outside_profile_fixed_size_sum H e 2 hDegree
    simpa only [f, hOutsideCard] using hSum
  have hExpanded :
      (∑ S ∈ (Finset.univ : Finset (Fin 5)).powersetCard 2, f S) =
        5 * f cycleFiveEdgePair + 5 * f cycleFiveDiagonalPair := by
    rw [cycleFive_pair_orbits_partition,
      Finset.sum_union cycleFive_pair_orbits_disjoint,
      cycleFive_orbit_weight_sum f hInv cycleFiveEdgePair,
      cycleFive_orbit_weight_sum f hInv cycleFiveDiagonalPair,
      cycleFive_edge_pair_orbit_card,
      cycleFive_diagonal_pair_orbit_card]
  have hWeights :
      f cycleFiveEdgePair + f cycleFiveDiagonalPair = 1 := by
    rw [hExpanded] at hTotal
    omega
  have hOrbitOne (P : Finset (Fin 5))
      (hP : f P = 1) (S : Finset (Fin 5))
      (hS : S ∈ cycleFiveSubsetOrbit P) : f S = 1 := by
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hS
    calc
      f S = f (P.image (Equiv.addRight d)) := by rw [hd]
      _ = f P := hInv P d
      _ = 1 := hP
  by_cases hEdge : f cycleFiveEdgePair = 1
  · have hBudget :
        (cycleFiveSubsetOrbit cycleFiveEdgePair).card =
          (finiteOutside e).card := by
      rw [cycleFive_edge_pair_orbit_card, hOutsideCard]
    obtain ⟨hImage,hInj⟩ :=
      outside_profile_canonical_image_of_unit_multiplicities
        H e (cycleFiveSubsetOrbit cycleFiveEdgePair) hBudget
        (hOrbitOne cycleFiveEdgePair hEdge)
    exact ⟨Or.inl hImage,hInj⟩
  · have hDiagonal : f cycleFiveDiagonalPair = 1 := by omega
    have hBudget :
        (cycleFiveSubsetOrbit cycleFiveDiagonalPair).card =
          (finiteOutside e).card := by
      rw [cycleFive_diagonal_pair_orbit_card,hOutsideCard]
    obtain ⟨hImage,hInj⟩ :=
      outside_profile_canonical_image_of_unit_multiplicities
        H e (cycleFiveSubsetOrbit cycleFiveDiagonalPair) hBudget
        (hOrbitOne cycleFiveDiagonalPair hDiagonal)
    exact ⟨Or.inr hImage,hInj⟩

end EPPAIII.BlockSystems
