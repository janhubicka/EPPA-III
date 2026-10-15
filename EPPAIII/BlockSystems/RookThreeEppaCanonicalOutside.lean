import EPPAIII.BlockSystems.RookThreeEppaCrossDegree
import EPPAIII.BlockSystems.RookThreeNeighbourhoodOrbits
import EPPAIII.BlockSystems.OutsideProfileCanonicalIndexing

/-!
# Canonical outside neighbourhood labels for the R3 exceptional case

For an 18-vertex EPPA host of the induced nine-vertex rook graph
whose outside vertices all have four selected neighbours, the
actual set of outside profiles is precisely one of the two
nine-element orbits: all open neighbourhoods of rook vertices,
or all strict nonneighbourhoods.

Each of these nine profiles occurs at one outside vertex and
at no other outside vertex. Thus every rook vertex canonically
labels a unique outside vertex, without an assumed identification
of the two host halves and without coherent EPPA lifts.

The adjacency relation inside the outside half and the final
vertex-transitivity obstruction remain separate obligations.
-/

namespace EPPAIII.BlockSystems

/-- Unit multiplicity propagates to the entire orbit under the
actual 72 rook automorphisms. -/
theorem rook_profile_unit_on_orbit
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (S : Finset rookVertex)
    (hUnit : outsideProfileMultiplicity H e S = 1)
    (T : Finset rookVertex) (hT : T ∈ rookSubsetOrbit S) :
    outsideProfileMultiplicity H e T = 1 := by
  classical
  obtain ⟨p,_,hEq⟩ := Finset.mem_image.mp hT
  calc
    outsideProfileMultiplicity H e T =
        outsideProfileMultiplicity H e
          (S.image (rookParameterizedAut p)) := by rw [hEq]
    _ = outsideProfileMultiplicity H e S :=
      (rook_outside_profile_multiplicity_invariant
        H e heppa S p).symm
    _ = 1 := hUnit

/-- The degree-four EPPA condition produces precisely one of the
two nine-element profile orbits, with no repeated outside profile. -/
theorem rook_eppa_degree_four_outside_profile_orbit
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (h18 : Fintype.card W = 18)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 4) :
    ((finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        rookSubsetOrbit rookFourSquare ∨
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        rookSubsetOrbit rookFourNineOther) ∧
      Set.InjOn (finiteNeighbourhoodProfile H e)
        (finiteOutside e : Set W) := by
  classical
  obtain ⟨hSum,_,_,_⟩ :=
    rook_eppa_outside_cross_degree_four_profile_classification
      H e heppa h18 hDegree
  by_cases hSquare : outsideProfileMultiplicity H e rookFourSquare = 1
  · have hBudget :
        (rookSubsetOrbit rookFourSquare).card =
          (finiteOutside e).card := by
      rw [rookFourSquare_orbit_card, rook_outside_card_nine e h18]
    have hOnce (S : Finset rookVertex) (hS : S ∈ rookSubsetOrbit rookFourSquare) :
        outsideProfileMultiplicity H e S = 1 :=
      rook_profile_unit_on_orbit H e heppa rookFourSquare hSquare S hS
    obtain ⟨hImage,hInj⟩ :=
      outside_profile_canonical_image_of_unit_multiplicities
        H e (rookSubsetOrbit rookFourSquare) hBudget hOnce
    exact ⟨Or.inl hImage,hInj⟩
  · have hOther :
        outsideProfileMultiplicity H e rookFourNineOther = 1 := by omega
    have hBudget :
        (rookSubsetOrbit rookFourNineOther).card =
          (finiteOutside e).card := by
      rw [rookFourNineOther_orbit_card, rook_outside_card_nine e h18]
    have hOnce (S : Finset rookVertex) (hS : S ∈ rookSubsetOrbit rookFourNineOther) :
        outsideProfileMultiplicity H e S = 1 :=
      rook_profile_unit_on_orbit H e heppa rookFourNineOther hOther S hS
    obtain ⟨hImage,hInj⟩ :=
      outside_profile_canonical_image_of_unit_multiplicities
        H e (rookSubsetOrbit rookFourNineOther) hBudget hOnce
    exact ⟨Or.inr hImage,hInj⟩

/-- Every base rook vertex has a unique outside representative whose
profile is its neighbourhood, or every base rook vertex has a unique
outside representative whose profile is its nonneighbourhood. -/
theorem rook_eppa_degree_four_canonical_outside_labels
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (h18 : Fintype.card W = 18)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 4) :
    (∀ x : rookVertex, ∃! w : W, w ∈ finiteOutside e ∧
      finiteNeighbourhoodProfile H e w = rookOpenNeighbourhood x) ∨
    (∀ x : rookVertex, ∃! w : W, w ∈ finiteOutside e ∧
      finiteNeighbourhoodProfile H e w = rookStrictNonneighbours x) := by
  classical
  obtain ⟨hCases,hInjective⟩ :=
    rook_eppa_degree_four_outside_profile_orbit H e heppa h18 hDegree
  have hUnique (E : Finset (Finset rookVertex))
      (label : rookVertex → Finset rookVertex)
      (hImage :
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) = E)
      (hMember : ∀ x : rookVertex, label x ∈ E) :
      ∀ x : rookVertex, ∃! w : W, w ∈ finiteOutside e ∧
        finiteNeighbourhoodProfile H e w = label x := by
    intro x
    have hx : label x ∈
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
      rw [hImage]
      exact hMember x
    obtain ⟨w,hw,hProfile⟩ := Finset.mem_image.mp hx
    refine ⟨w,⟨hw,hProfile⟩,?_⟩
    intro v hv
    exact hInjective hv.1 hw (hv.2.trans hProfile.symm)
  rcases hCases with hSquare | hOther
  · right
    apply hUnique (rookSubsetOrbit rookFourSquare)
      rookStrictNonneighbours hSquare
    intro x
    rw [rook_other_nine_orbit_eq_nonneighbourhoods]
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  · left
    apply hUnique (rookSubsetOrbit rookFourNineOther)
      rookOpenNeighbourhood hOther
    intro x
    rw [rook_nine_orbit_eq_neighbourhoods]
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩

end EPPAIII.BlockSystems
