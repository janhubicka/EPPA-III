import EPPAIII.BlockSystems.OutsideProfileMultiplicity

/-!
# Canonical outside labels from saturated EPPA profile multiplicities

Suppose a finite collection E of selected-base neighbourhood profiles
has as many elements as the complementary half of an EPPA host, and
every profile in E occurs exactly once among outside vertices.

Then the actual outside-profile image is precisely E and the profile
map is injective on the outside vertices. Consequently each label
in E has a unique outside witness.

This general lemma does not assume coherent EPPA lifts or an a priori
outside labelling. In R3 it will index the outside by a nine-point orbit.
-/

namespace EPPAIII.BlockSystems

/-- A saturated family of profiles is exactly the outside image,
and provides unique labels for outside vertices. -/
theorem outside_profile_canonical_image_of_unit_multiplicities
    {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W)
    (E : Finset (Finset V))
    (hBudget : E.card = (finiteOutside e).card)
    (hOnce : ∀ S ∈ E, outsideProfileMultiplicity H e S = 1) :
    (finiteOutside e).image (finiteNeighbourhoodProfile H e) = E ∧
      Set.InjOn (finiteNeighbourhoodProfile H e)
        (finiteOutside e : Set W) := by
  classical
  have hRealised (S : Finset V) (hS : S ∈ E) :
      ∃ w : W, w ∈ finiteOutside e ∧
        finiteNeighbourhoodProfile H e w = S := by
    have hc := hOnce S hS
    unfold outsideProfileMultiplicity at hc
    have hPositive :
        0 < ((finiteOutside e).filter
          (fun w => finiteNeighbourhoodProfile H e w = S)).card := by
      omega
    obtain ⟨w,hw⟩ := Finset.card_pos.mp hPositive
    obtain ⟨hwOut,hwProfile⟩ := Finset.mem_filter.mp hw
    exact ⟨w,hwOut,hwProfile⟩
  have hSubset :
      E ⊆ (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
    intro S hS
    obtain ⟨w,hwOut,hwProfile⟩ := hRealised S hS
    exact Finset.mem_image.mpr ⟨w,hwOut,hwProfile⟩
  have hBound :
      ((finiteOutside e).image (finiteNeighbourhoodProfile H e)).card
        ≤ E.card := by
    calc
      ((finiteOutside e).image (finiteNeighbourhoodProfile H e)).card
          ≤ (finiteOutside e).card := Finset.card_image_le
      _ = E.card := hBudget.symm
  have hEq : E = (finiteOutside e).image
      (finiteNeighbourhoodProfile H e) :=
    Finset.eq_of_subset_of_card_le hSubset hBound
  have hCardImage :
      ((finiteOutside e).image (finiteNeighbourhoodProfile H e)).card =
        (finiteOutside e).card := by
    rw [← hEq]
    exact hBudget
  exact ⟨hEq.symm, Finset.injOn_of_card_image_eq hCardImage⟩

/-- Every canonical profile has exactly one outside representative. -/
theorem outside_profile_unique_of_unit_multiplicities
    {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W)
    (E : Finset (Finset V))
    (hBudget : E.card = (finiteOutside e).card)
    (hOnce : ∀ S ∈ E, outsideProfileMultiplicity H e S = 1)
    (S : Finset V) (hS : S ∈ E) :
    ∃! w : W, w ∈ finiteOutside e ∧
      finiteNeighbourhoodProfile H e w = S := by
  obtain ⟨hImage,hInjective⟩ :=
    outside_profile_canonical_image_of_unit_multiplicities
      H e E hBudget hOnce
  have hInImage :
      S ∈ (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
    rw [hImage]
    exact hS
  obtain ⟨w,hwOut,hwProfile⟩ := Finset.mem_image.mp hInImage
  refine ⟨w,⟨hwOut,hwProfile⟩,?_⟩
  intro v hv
  exact hInjective hv.1 hwOut (hv.2.trans hwProfile.symm)

end EPPAIII.BlockSystems
