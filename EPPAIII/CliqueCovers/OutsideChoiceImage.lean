import EPPAIII.CliqueCovers.OutsideChoiceEquivalence

/-!
# Exact image of saturated outside-coordinate choices

In the direct Section 3 proof, a saturated profile orbit gives a
bijection from the st outside vertices to the formal choices of
r clique positions carrying k-subsets.  The earlier theorem
`eppa_saturated_choice_existsUnique_outside` gives a witness for
every admissible choice.  Here we also show *there are no other
choices*: the image of the actual extraction map is exactly the
finite choice space.  This is the convenient finite-set interface
for transporting the graph on the complementary half.

Nothing here assumes an outside clique partition, transitivity of
the host, or coherent choices of EPPA extension automorphisms.
-/

namespace EPPAIII.CliqueCovers

/-- Saturation gives *equality* of the actual finite outside-choice
image and the combinatorial choice space. -/
theorem eppa_saturated_outside_choice_image_eq {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t) :
    (finiteOutside e).image
      (fun u => extractKChoice (finiteNeighbourhoodProfile H e u) k) =
      profileChoiceSpace s t r k := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro choice hChoice
    obtain ⟨u, ⟨hu, hcu⟩, _⟩ :=
      eppa_saturated_choice_existsUnique_outside
        H e heppa hOrder w hw r k hR hSat choice hChoice
    exact Finset.mem_image.mpr ⟨u, hu, hcu⟩
  · calc
      ((finiteOutside e).image
        (fun u => extractKChoice (finiteNeighbourhoodProfile H e u) k)).card
          ≤ (finiteOutside e).card := Finset.card_image_le
      _ = s * t := finiteOutside_card_clique_union e hOrder
      _ = (profileChoiceSpace s t r k).card := by
        rw [profileChoiceSpace_card, hSat]

/-- Every outside vertex really does extract an admissible choice;
this is the nontrivial reverse inclusion after saturation. -/
theorem eppa_saturated_outside_choice_mem {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (u : W) (hu : u ∈ finiteOutside e) :
    extractKChoice (finiteNeighbourhoodProfile H e u) k ∈
      profileChoiceSpace s t r k := by
  classical
  rw [← eppa_saturated_outside_choice_image_eq
    H e heppa hOrder w hw r k hR hSat]
  exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

end EPPAIII.CliqueCovers
