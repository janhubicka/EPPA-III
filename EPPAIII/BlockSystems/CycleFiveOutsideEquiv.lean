import EPPAIII.BlockSystems.CycleFiveOutsideProfileSaturation
import EPPAIII.BlockSystems.RookThreeOutsideEquiv

/-!
# Canonical C5 outside labels, without an outside partition hypothesis

When an actual ten-vertex EPPA witness for the five-cycle has two
selected neighbours at every outside vertex, its five profiles form
exactly one of the two cyclic pair orbits, each occurring once.

The orbit is indexed by the five translations of the pair {0,1}
or {0,2}. Both label functions are injective. Thus the generic
outside-profile equivalence theorem constructs a genuine equivalence
from Fin 5 onto the five outside vertices preserving every profile.

This is stronger than excluding a canonical C4+C6 incidence matrix:
it gives the actual cross-incidence classification without ever
enumerating arbitrary disconnected 2-regular bipartite graphs.
-/

namespace EPPAIII.BlockSystems

/-- Adjacent-pair profiles and diagonal-pair profiles indexed by a shift. -/
def cycleFiveEdgePairShift (d : Fin 5) : Finset (Fin 5) :=
  cycleFiveEdgePair.image (Equiv.addRight d)

def cycleFiveDiagonalPairShift (d : Fin 5) : Finset (Fin 5) :=
  cycleFiveDiagonalPair.image (Equiv.addRight d)

/-- Both cyclic pair-profile parametrisations are injective. -/
theorem cycleFive_edge_pair_shift_injective :
    Function.Injective cycleFiveEdgePairShift := by
  decide

theorem cycleFive_diagonal_pair_shift_injective :
    Function.Injective cycleFiveDiagonalPairShift := by
  decide

/-- The genuine complementary half has canonical cyclic coordinates,
induced solely by its actual selected neighbourhood profiles. -/
theorem cycleFive_eppa_outside_equiv_of_two_neighbours
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 2) :
    ∃ f : (Fin 5) ≃ {w : W // w ∈ finiteOutside e},
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (f x).val =
          cycleFiveEdgePairShift x) ∨
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (f x).val =
          cycleFiveDiagonalPairShift x) := by
  classical
  obtain ⟨hCases,hInjective⟩ :=
    cycleFive_eppa_outside_pair_profile_classification
      H e heppa hTen hDegree
  rcases hCases with hEdge | hDiagonal
  · have hImage :
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
          (Finset.univ : Finset (Fin 5)).image cycleFiveEdgePairShift := by
      simpa only [cycleFiveSubsetOrbit,cycleFiveEdgePairShift] using hEdge
    obtain ⟨f,hf⟩ := outside_profile_label_family_equiv
      H e cycleFiveEdgePairShift
      cycleFive_edge_pair_shift_injective hImage hInjective
    exact ⟨f,Or.inl hf⟩
  · have hImage :
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
          (Finset.univ : Finset (Fin 5)).image cycleFiveDiagonalPairShift := by
      simpa only [cycleFiveSubsetOrbit,cycleFiveDiagonalPairShift] using hDiagonal
    obtain ⟨f,hf⟩ := outside_profile_label_family_equiv
      H e cycleFiveDiagonalPairShift
      cycleFive_diagonal_pair_shift_injective hImage hInjective
    exact ⟨f,Or.inr hf⟩

/-- In particular, there cannot be two different outside vertices
with the same pair of selected neighbours. This directly excludes
any disconnected C4+C6 cross-incidence candidate without labelling it. -/
theorem cycleFive_eppa_no_repeated_outside_pair_profiles
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 2)
    (u v : W) (hu : u ∈ finiteOutside e)
    (hv : v ∈ finiteOutside e)
    (hEqual : finiteNeighbourhoodProfile H e u =
      finiteNeighbourhoodProfile H e v) :
    u = v :=
  (cycleFive_eppa_outside_pair_profile_classification
    H e heppa hTen hDegree).2 hu hv hEqual

end EPPAIII.BlockSystems
