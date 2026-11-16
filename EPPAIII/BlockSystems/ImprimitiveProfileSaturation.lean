import EPPAIII.BlockSystems.OutsideOrbitSaturation
import EPPAIII.BlockSystems.RookThreeOutsideEquiv
import EPPAIII.BlockSystems.OutsideProfileCanonicalAction

/-!
# A common EPPA outside-profile argument for the imprimitive exceptions

The C5 and 3x3 rook cases in Section 6 use the same three steps:
1. a full orbit of selected-neighbourhood profiles exhausts the outside half;
2. each profile labels a unique actual outside vertex;
3. genuine EPPA extensions of base automorphisms force the action on these labels.

This theorem packages the three steps without assuming coherent choices of
EPPA extensions, an action on the outside half, or a pre-labelled outside copy.
It serves the Section 6 English-proof audit as a single reusable interface.

The theorem does *not* classify the outside adjacency graph: orbit-invariant
edge choices and the vertex-transitivity/triangle-count exclusions remain
separate obligations in the C5 and rook modules.
-/

namespace EPPAIII.BlockSystems

/-- If an orbit of selected-neighbourhood profiles exhausts the outside
vertex budget, and is parametrised injectively by the base vertices,
the complementary half has a uniquely determined labelling.

Every base automorphism compatible with that labelling acts by a genuine
automorphism of the outside induced graph. Its lift is chosen separately
for each automorphism; no group-action coherence is assumed. -/
theorem eppa_saturated_outside_labels_and_action
    {V W I : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [Fintype I]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (p : I → Equiv.Perm V)
    (hp : ∀ i : I, IsGraphAutomorphism G (p i))
    (w : W) (hw : w ∈ finiteOutside e)
    (hBudget :
      ((Finset.univ : Finset I).image
        (fun i => (finiteNeighbourhoodProfile H e w).image (p i))).card =
          (finiteOutside e).card)
    (label : V → Finset V)
    (hLabelInj : Function.Injective label)
    (hOrbit :
      (Finset.univ : Finset I).image
        (fun i => (finiteNeighbourhoodProfile H e w).image (p i)) =
          (Finset.univ : Finset V).image label) :
    ∃ f : V ≃ {v : W // v ∈ finiteOutside e},
      (∀ x : V,
        finiteNeighbourhoodProfile H e (f x).val = label x) ∧
      (∀ q : Equiv.Perm V, IsGraphAutomorphism G q →
        (∀ x : V, label (q x) = (label x).image q) →
        IsGraphAutomorphism (H.comap (fun x => (f x).val)) q) := by
  classical
  obtain ⟨hImageOrbit,hProfileInjective⟩ :=
    eppa_outside_orbit_saturation_of_card
      G H e heppa p hp w hw hBudget
  have hImage :
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        (Finset.univ : Finset V).image label :=
    hImageOrbit.trans hOrbit
  obtain ⟨f,hProfiles⟩ :=
    outside_profile_label_family_equiv
      H e label hLabelInj hImage hProfileInjective
  refine ⟨f,hProfiles,?_⟩
  intro q hq hLabelEq
  exact canonical_outside_graph_automorphism
    G H e heppa q hq label (fun x => (f x).val)
    (fun x => (f x).property) hProfiles hProfileInjective hLabelEq

end EPPAIII.BlockSystems
