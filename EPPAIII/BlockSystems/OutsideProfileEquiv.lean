import EPPAIII.BlockSystems.OutsideProfileCanonicalIndexing

/-!
# Canonical equivalence between outside vertices and their profiles

Once the actual outside-profile image is a known finite family E
and the profile map is injective on the outside half, it is a genuine
bijection from the outside vertex subtype to the profile subtype.

This is the graph-independent reusable interface needed to transport
the adjacency relation on the complementary half into canonical
profile coordinates. No equivariant choice of EPPA lifts is assumed;
the equivalence comes solely from the actual injective profile map.
-/

namespace EPPAIII.BlockSystems

/-- Every injective outside-profile map induces a canonical
equivalence from outside host vertices to the attained profiles. -/
theorem exists_outside_profile_equiv_of_image_injective
    {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W)
    (E : Finset (Finset V))
    (hImage :
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) = E)
    (hInj : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W)) :
    ∃ φ : ↥(finiteOutside e) ≃ ↥E,
      ∀ w : ↥(finiteOutside e),
        (φ w).val = finiteNeighbourhoodProfile H e w.val := by
  classical
  let f : ↥(finiteOutside e) → ↥E := fun w =>
    ⟨finiteNeighbourhoodProfile H e w.val, by
      rw [← hImage]
      exact Finset.mem_image.mpr ⟨w.val,w.property,rfl⟩⟩
  have hfInj : Function.Injective f := by
    intro w w' h
    apply Subtype.ext
    exact hInj w.property w'.property
      (congrArg Subtype.val h)
  have hfSurj : Function.Surjective f := by
    intro S
    have hS : S.val ∈
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
      rw [hImage]
      exact S.property
    obtain ⟨w,hw,hProfile⟩ := Finset.mem_image.mp hS
    refine ⟨⟨w,hw⟩,?_⟩
    apply Subtype.ext
    exact hProfile
  refine ⟨Equiv.ofBijective f ⟨hfInj,hfSurj⟩,?_⟩
  intro w
  rfl

/-- Unit multiplicity on a saturated family is enough to construct
the canonical outside vertex/profile equivalence directly. -/
theorem exists_outside_profile_equiv_of_unit_multiplicities
    {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W)
    (E : Finset (Finset V))
    (hBudget : E.card = (finiteOutside e).card)
    (hOnce : ∀ S ∈ E, outsideProfileMultiplicity H e S = 1) :
    ∃ φ : ↥(finiteOutside e) ≃ ↥E,
      ∀ w : ↥(finiteOutside e),
        (φ w).val = finiteNeighbourhoodProfile H e w.val := by
  obtain ⟨hImage,hInj⟩ :=
    outside_profile_canonical_image_of_unit_multiplicities
      H e E hBudget hOnce
  exact exists_outside_profile_equiv_of_image_injective
    H e E hImage hInj

end EPPAIII.BlockSystems
