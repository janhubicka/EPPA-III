import EPPAIII.BlockSystems.CycleFivePairProfileOrbits

/-!
# Saturation by any nontrivial C5 outside profile

A ten-vertex EPPA witness of an induced five-cycle has five
complementary vertices. The five genuine rotations of the selected
C5 act freely on *every* nonempty proper subset of its five vertices.
Consequently a single outside vertex with a nonempty proper selected
neighbourhood already exhausts the entire outside vertex budget:
its five cyclic profile translates are realised, without repeats.

The only other possibility is that every outside profile is
either empty or the full selected five-cycle. In particular,
in the proper-profile case no assumption of uniform outside
cross-degree, outside transitivity, invariant two-point fibres,
or coherent EPPA lifts is needed.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- The cyclic action of order five is free on every nonempty,
non-full subset of the five-cycle's vertex set. This checks all
32 subsets and is independent of any ambient host graph. -/
theorem cycleFive_proper_subset_orbit_size :
    ∀ S : Finset (Fin 5),
      S ≠ ∅ →
      S ≠ (Finset.univ : Finset (Fin 5)) →
      (cycleFiveSubsetOrbit S).card = 5 := by
  decide

/-- If one actual outside vertex has a proper nonempty selected
neighbourhood, then the actual five outside profiles are exactly
its five different cyclic translates. In particular the outside
profile map is injective and uniform cross-degree is a conclusion,
rather than a hypothesis. -/
theorem cycleFive_eppa_proper_profile_saturates_outside
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hNonempty :
      finiteNeighbourhoodProfile H e w ≠ ∅)
    (hNonfull :
      finiteNeighbourhoodProfile H e w ≠
        (Finset.univ : Finset (Fin 5))) :
    (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        cycleFiveSubsetOrbit (finiteNeighbourhoodProfile H e w) ∧
      Set.InjOn (finiteNeighbourhoodProfile H e)
        (finiteOutside e : Set W) := by
  classical
  let S : Finset (Fin 5) := finiteNeighbourhoodProfile H e w
  have hOrbitCard : (cycleFiveSubsetOrbit S).card = 5 :=
    cycleFive_proper_subset_orbit_size S hNonempty hNonfull
  have hOutsideCard : (finiteOutside e).card = 5 := by
    have hCard := finiteOutside_card e
    have hBase : Fintype.card (Fin 5) = 5 := by decide
    omega
  have hSPositive : 0 < outsideProfileMultiplicity H e S := by
    unfold outsideProfileMultiplicity
    apply Finset.card_pos.mpr
    exact ⟨w, Finset.mem_filter.mpr ⟨hw,rfl⟩⟩
  have hOrbitRealised :
      cycleFiveSubsetOrbit S ⊆
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
    intro T hT
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hT
    have hTPositive : 0 < outsideProfileMultiplicity H e T := by
      rw [← hd, cycleFive_outside_profile_multiplicity_invariant
        H e heppa S d]
      exact hSPositive
    unfold outsideProfileMultiplicity at hTPositive
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hTPositive
    obtain ⟨hvOut,hvProfile⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_image.mpr ⟨v,hvOut,hvProfile⟩
  have hImageBound :
      ((finiteOutside e).image (finiteNeighbourhoodProfile H e)).card
        ≤ (cycleFiveSubsetOrbit S).card := by
    calc
      _ ≤ (finiteOutside e).card := Finset.card_image_le
      _ = 5 := hOutsideCard
      _ = (cycleFiveSubsetOrbit S).card := hOrbitCard.symm
  have hOrbitEquals :
      cycleFiveSubsetOrbit S =
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) :=
    Finset.eq_of_subset_of_card_le hOrbitRealised hImageBound
  have hImageCard :
      ((finiteOutside e).image (finiteNeighbourhoodProfile H e)).card
        = (finiteOutside e).card := by
    rw [← hOrbitEquals, hOrbitCard, hOutsideCard]
  exact ⟨hOrbitEquals.symm, Finset.injOn_of_card_image_eq hImageCard⟩

/-- Complete C5 profile dichotomy for an actual ten-vertex
EPPA witness. Either every outside neighbourhood is empty or
full, or one proper orbit labels all five outside vertices. -/
theorem cycleFive_eppa_outside_profile_dichotomy
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10) :
    (∀ w : W, w ∈ finiteOutside e →
      finiteNeighbourhoodProfile H e w = ∅ ∨
      finiteNeighbourhoodProfile H e w =
        (Finset.univ : Finset (Fin 5))) ∨
    ∃ (w : W) (hw : w ∈ finiteOutside e),
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        cycleFiveSubsetOrbit (finiteNeighbourhoodProfile H e w) ∧
      Set.InjOn (finiteNeighbourhoodProfile H e)
        (finiteOutside e : Set W) := by
  classical
  by_cases hProper : ∃ w : W, w ∈ finiteOutside e ∧
      finiteNeighbourhoodProfile H e w ≠ ∅ ∧
      finiteNeighbourhoodProfile H e w ≠
        (Finset.univ : Finset (Fin 5))
  · right
    obtain ⟨w,hw,hNe,hFull⟩ := hProper
    exact ⟨w,hw,
      cycleFive_eppa_proper_profile_saturates_outside
        H e heppa hTen w hw hNe hFull⟩
  · left
    intro w hw
    by_cases hEmpty : finiteNeighbourhoodProfile H e w = ∅
    · exact Or.inl hEmpty
    · right
      by_contra hFull
      exact hProper ⟨w,hw,hEmpty,hFull⟩

end EPPAIII.BlockSystems
