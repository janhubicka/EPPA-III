import EPPAIII.BlockSystems.OutsideProfileMultiplicity

/-!
# Saturating an EPPA outside half by a full base-automorphism orbit

An outside neighbourhood profile of a distinguished induced base
G has a finite orbit under any indexed family of genuine base
automorphisms. Every profile in that orbit is realised by some
complementary host vertex, by extending a base automorphism once;
no coherent choice of lifts is needed.

If the orbit already has as many elements as the entire outside
half, the outside profile image equals that orbit and profiles
injectively label the outside vertices.

This result is independent of the shape of G and unifies the
five-cycle and nine-vertex rook exceptional arguments.
-/

namespace EPPAIII.BlockSystems

/-- A full finite orbit of the initial profile exhausts the
complementary host as soon as its cardinality equals the
outside vertex budget. Each outside profile then occurs once. -/
theorem eppa_outside_orbit_saturation_of_card
    {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [Fintype I]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (p : I → Equiv.Perm V)
    (hp : ∀ i : I, IsGraphAutomorphism G (p i))
    (w : W) (hw : w ∈ finiteOutside e)
    (hBudget :
      ((Finset.univ : Finset I).image
        (fun i =>
          (finiteNeighbourhoodProfile H e w).image (p i))).card =
        (finiteOutside e).card) :
    (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
      (Finset.univ : Finset I).image
        (fun i =>
          (finiteNeighbourhoodProfile H e w).image (p i)) ∧
    Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W) := by
  classical
  let P : Finset V := finiteNeighbourhoodProfile H e w
  let O : Finset (Finset V) :=
    (Finset.univ : Finset I).image (fun i => P.image (p i))
  have hPositive : 0 < outsideProfileMultiplicity H e P := by
    letI : DecidableEq V := Classical.decEq _
    unfold outsideProfileMultiplicity
    apply Finset.card_pos.mpr
    exact ⟨w,Finset.mem_filter.mpr ⟨hw,rfl⟩⟩
  have hRealised :
      O ⊆ (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
    intro T hT
    obtain ⟨i,_,hTi⟩ := Finset.mem_image.mp hT
    have hPosT : 0 < outsideProfileMultiplicity H e T := by
      rw [← hTi,
        ← outside_profile_multiplicity_base_automorphism
          G H e heppa (p i) (hp i) P]
      exact hPositive
    have hExists : ∃ v : W, v ∈ finiteOutside e ∧
        finiteNeighbourhoodProfile H e v = T := by
      letI : DecidableEq V := Classical.decEq _
      unfold outsideProfileMultiplicity at hPosT
      obtain ⟨v,hv⟩ := Finset.card_pos.mp hPosT
      obtain ⟨hvOut,hvProfile⟩ := Finset.mem_filter.mp hv
      exact ⟨v,hvOut,hvProfile⟩
    obtain ⟨v,hvOut,hvProfile⟩ := hExists
    exact Finset.mem_image.mpr ⟨v,hvOut,hvProfile⟩
  have hCardBound :
      ((finiteOutside e).image (finiteNeighbourhoodProfile H e)).card
        ≤ O.card := by
    calc
      _ ≤ (finiteOutside e).card := Finset.card_image_le
      _ = O.card := hBudget.symm
  have hOrbitEquals :
      O = (finiteOutside e).image (finiteNeighbourhoodProfile H e) :=
    Finset.eq_of_subset_of_card_le hRealised hCardBound
  have hImageCard :
      ((finiteOutside e).image (finiteNeighbourhoodProfile H e)).card =
        (finiteOutside e).card := by
    rw [← hOrbitEquals]
    exact hBudget
  exact ⟨hOrbitEquals.symm,
    Finset.injOn_of_card_image_eq hImageCard⟩

end EPPAIII.BlockSystems
