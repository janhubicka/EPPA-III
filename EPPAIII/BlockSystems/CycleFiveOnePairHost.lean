import EPPAIII.BlockSystems.CycleFiveProperProfileSaturation
import EPPAIII.BlockSystems.CycleFiveDoubleClassification

/-!
# Removing the uniform-cross-degree hypothesis in the C5 branch

The free orbit of any nontrivial outside profile fills all five
outside vertices in an order-ten EPPA witness for the five-cycle.
Every cyclic translate has the same cardinality. Hence every
proper-profile orbit has constant cross-degree, without assuming
a transitive action on the outside half or a priori outside blocks.

Combined with the verified degree-two graph classification, just
one outside vertex with two selected neighbours suffices to
identify the entire host as one of the two cyclic doubles.
-/

namespace EPPAIII.BlockSystems

/-- If any outside profile is nonempty and proper, all outside
vertices have exactly the same number of selected neighbours.
This follows from actual EPPA profile saturation, not from a
chosen transitive outside action. -/
theorem cycleFive_eppa_proper_outside_degree_uniform
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hNonempty : finiteNeighbourhoodProfile H e w ≠ ∅)
    (hNonfull : finiteNeighbourhoodProfile H e w ≠
      (Finset.univ : Finset (Fin 5)))
    (v : W) (hv : v ∈ finiteOutside e) :
    (finiteNeighbourhoodProfile H e v).card =
      (finiteNeighbourhoodProfile H e w).card := by
  classical
  have hImage :=
    (cycleFive_eppa_proper_profile_saturates_outside
      H e heppa hTen w hw hNonempty hNonfull).1
  have hMember : finiteNeighbourhoodProfile H e v ∈
      cycleFiveSubsetOrbit (finiteNeighbourhoodProfile H e w) := by
    rw [← hImage]
    exact Finset.mem_image.mpr ⟨v,hv,rfl⟩
  obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hMember
  calc
    (finiteNeighbourhoodProfile H e v).card =
        ((finiteNeighbourhoodProfile H e w).image
          (Equiv.addRight d)).card := by rw [hd]
    _ = (finiteNeighbourhoodProfile H e w).card :=
      Finset.card_image_of_injective _
        (Equiv.addRight d).injective

/-- Any one outside vertex of cross-degree two forces every
outside vertex to have cross-degree two. -/
theorem cycleFive_eppa_one_outside_pair_forces_uniform
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hPair : (finiteNeighbourhoodProfile H e w).card = 2) :
    ∀ v : W, v ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e v).card = 2 := by
  classical
  have hNonempty : finiteNeighbourhoodProfile H e w ≠ ∅ := by
    intro hEmpty
    have hZero : (finiteNeighbourhoodProfile H e w).card = 0 := by
      rw [hEmpty]
      simp
    omega
  have hNonfull : finiteNeighbourhoodProfile H e w ≠
      (Finset.univ : Finset (Fin 5)) := by
    intro hFull
    have hFive : (finiteNeighbourhoodProfile H e w).card = 5 := by
      rw [hFull]
      decide
    omega
  intro v hv
  calc
    (finiteNeighbourhoodProfile H e v).card =
        (finiteNeighbourhoodProfile H e w).card :=
      cycleFive_eppa_proper_outside_degree_uniform
        H e heppa hTen w hw hNonempty hNonfull v hv
    _ = 2 := hPair

/-- A single two-neighbour outside vertex suffices for the
complete graph-level C5 degree-two classification. The old
global uniformity assumption is now a verified consequence. -/
theorem cycleFive_eppa_one_outside_pair_host_classification
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hPair : (finiteNeighbourhoodProfile H e w).card = 2) :
    ∃ (phi : Bool × Fin 5 ≃ W) (diagonal : Bool),
      (∀ x : Fin 5, phi (false,x) = e x) ∧
      H.comap phi = cycleFiveDoubleGraph false diagonal := by
  exact cycleFive_eppa_degree_two_host_is_cyclic_double
    H e heppa hTrans hTen
      (cycleFive_eppa_one_outside_pair_forces_uniform
        H e heppa hTen w hw hPair)

end EPPAIII.BlockSystems
