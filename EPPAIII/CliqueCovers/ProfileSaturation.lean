import EPPAIII.CliqueCovers.Claim39OrbitBridge

/-!
# Saturated neighbourhood-profile choices

The existing wreath-choice realisability theorem supplies a surjection
from a finite orbit of neighbourhood profiles onto all prescribed
size-k coordinate choices. If the number of available profiles is
at most the number of such choices, this surjection is injective.

This is the key rigidity input for excluding a second independently
movable partial coordinate after the Claim 3.9 orbit estimate has
saturated the outside half of a double-sized EPPA witness.

No regularity or stability of outside cliques is assumed.
-/

namespace EPPAIII.CliqueCovers

/-- If the number of wreath translates is at most the number of
independent r-coordinate k-subset choices, those choices uniquely
determine the translated profile. -/
theorem extractKChoice_injOn_of_orbit_le_choices {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (r k : ℕ)
    (hR : (kPositions P k).card = r)
    (hBound : (wreathOrbit P).card ≤
      (Nat.choose s r) * (Nat.choose t k)^r) :
    Set.InjOn (fun Q => extractKChoice Q k)
      ↑(wreathOrbit P) := by
  classical
  have hSubset :
      profileChoiceSpace s t r k ⊆
        (wreathOrbit P).image (fun Q => extractKChoice Q k) := by
    intro choice hc
    obtain ⟨Q,hQ,hChoice⟩ :=
      wreath_choice_realisable P r k hR choice hc
    exact Finset.mem_image.mpr ⟨Q,hQ,hChoice⟩
  have hBound' :
      (wreathOrbit P).card ≤
        (profileChoiceSpace s t r k).card := by
    simpa only [profileChoiceSpace_card] using hBound
  have hLower :
      (profileChoiceSpace s t r k).card ≤
        ((wreathOrbit P).image (fun Q => extractKChoice Q k)).card :=
    Finset.card_le_card hSubset
  have hUpper :
      ((wreathOrbit P).image (fun Q => extractKChoice Q k)).card ≤
        (wreathOrbit P).card :=
    Finset.card_image_le
  have hImageEq :
      ((wreathOrbit P).image (fun Q => extractKChoice Q k)).card =
        (wreathOrbit P).card := by
    omega
  exact Finset.injOn_of_card_image_eq hImageEq

/-- For a double-sized EPPA witness, equality between the
parameter-space count and the number of outside vertices forces
the selected size-k coordinate data to determine the *entire*
wreath orbit profile. No hypothesis about individual D_j is used. -/
theorem extractKChoice_injOn_of_eppa_double {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : (Nat.choose s r) * (Nat.choose t k)^r = s * t) :
    Set.InjOn (fun Q => extractKChoice Q k)
      ↑(wreathOrbit (finiteNeighbourhoodProfile H e w)) := by
  apply extractKChoice_injOn_of_orbit_le_choices
    (finiteNeighbourhoodProfile H e w) r k hR
  calc
    (wreathOrbit (finiteNeighbourhoodProfile H e w)).card ≤
        (finiteProfileOrbit (cliqueUnion s t) H e w).card :=
      Finset.card_le_card
        (wreathOrbit_subset_finiteProfileOrbit H e w)
    _ ≤ (finiteOutside e).card :=
      finite_profile_orbit_card_le_outside
        (cliqueUnion s t) H e heppa w hw
    _ = s * t := finiteOutside_card_clique_union e hOrder
    _ = (Nat.choose s r) * (Nat.choose t k)^r := hSat.symm

end EPPAIII.CliqueCovers
