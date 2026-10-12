import EPPAIII.CliqueCovers.OutsideProfileBijection
import EPPAIII.CliqueCovers.ProfileSaturation

/-!
# Saturated outside vertices correspond to finite coordinate choices

When a size-k neighbourhood profile orbit saturates the st available
outside vertices, the concrete wreath orbit, the full base
automorphism profile orbit, and the set of outside profiles agree.

More precisely, every formal r-position/k-subset choice is realised
by exactly one outside vertex. Thus no arbitrary choice of EPPA
extensions is needed to label the complementary half by the same
parameter space used in the wreath orbit argument.

The next step is to identify the unique-coordinate k=1 or k=t-1
choice space with the natural Fin s × Fin t representation and
transport the graph adjacency to this representation.
-/

namespace EPPAIII.CliqueCovers

/-- At saturation, the concrete wreath orbit already exhausts
the larger orbit under every automorphism of the selected graph. -/
theorem eppa_saturated_wreath_equals_full_orbit {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t) :
    wreathOrbit (finiteNeighbourhoodProfile H e w) =
      finiteProfileOrbit (cliqueUnion s t) H e w := by
  classical
  have hSubset :=
    wreathOrbit_subset_finiteProfileOrbit H e w
  apply Finset.eq_of_subset_of_card_le hSubset
  calc
    (finiteProfileOrbit (cliqueUnion s t) H e w).card ≤
        (finiteOutside e).card :=
      finite_profile_orbit_card_le_outside
        (cliqueUnion s t) H e heppa w hw
    _ = s * t := finiteOutside_card_clique_union e hOrder
    _ = Nat.choose s r * (Nat.choose t k)^r := hSat.symm
    _ ≤ (wreathOrbit (finiteNeighbourhoodProfile H e w)).card :=
      wreath_orbit_card_lower_bound
        (finiteNeighbourhoodProfile H e w) r k hR

/-- Under saturation, the selected-coordinate choice extraction
is injective on the entire outside half. -/
theorem eppa_saturated_outside_choice_injective {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t) :
    Set.InjOn (fun u : W =>
      extractKChoice (finiteNeighbourhoodProfile H e u) k)
      {u | u ∈ finiteOutside e} := by
  classical
  have hOrbitEq :=
    eppa_saturated_wreath_equals_full_orbit
      H e heppa hOrder w hw r k hR hSat
  have hOut :=
    eppa_saturated_outside_profile_bijection
      H e heppa hOrder w hw r k hR hSat
  have hExtract :=
    extractKChoice_injOn_of_eppa_double
      H e heppa hOrder w hw r k hR hSat
  intro u hu v hv hChoice
  have huOrbit :
      finiteNeighbourhoodProfile H e u ∈
        wreathOrbit (finiteNeighbourhoodProfile H e w) := by
    rw [hOrbitEq]
    exact hOut.2 u hu
  have hvOrbit :
      finiteNeighbourhoodProfile H e v ∈
        wreathOrbit (finiteNeighbourhoodProfile H e w) := by
    rw [hOrbitEq]
    exact hOut.2 v hv
  have hProfileEq :=
    hExtract huOrbit hvOrbit hChoice
  exact hOut.1 hu hv hProfileEq

/-- Every formal choice of r size-k coordinates is realised by
exactly one vertex of the outside half. -/
theorem eppa_saturated_choice_existsUnique_outside {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (choice : Σ R : Finset (Fin s), ∀ i : Fin s, i ∈ R → Finset (Fin t))
    (hChoice : choice ∈ profileChoiceSpace s t r k) :
    ∃! u : W, u ∈ finiteOutside e ∧
      extractKChoice (finiteNeighbourhoodProfile H e u) k = choice := by
  classical
  let P := finiteNeighbourhoodProfile H e w
  obtain ⟨Q, hQ, hQChoice⟩ :=
    wreath_choice_realisable P r k hR choice hChoice
  have hFullOrbit : Q ∈
      finiteProfileOrbit (cliqueUnion s t) H e w :=
    (wreathOrbit_subset_finiteProfileOrbit H e w) hQ
  have hImage : Q ∈ finiteOutsideProfileImage H e :=
    (finite_profile_orbit_subset_outside_image
      (cliqueUnion s t) H e heppa w hw) hFullOrbit
  have hImage' : Q ∈ (finiteOutside e).image
      (finiteNeighbourhoodProfile H e) := by
    simpa [finiteOutsideProfileImage] using hImage
  obtain ⟨u, huOutside, huProfile⟩ := Finset.mem_image.mp hImage'
  have huChoice :
      extractKChoice (finiteNeighbourhoodProfile H e u) k = choice := by
    rw [huProfile]
    exact hQChoice
  have hInjective :=
    eppa_saturated_outside_choice_injective
      H e heppa hOrder w hw r k hR hSat
  refine ⟨u, ⟨huOutside, huChoice⟩, ?_⟩
  intro v hv
  have hEqualChoices :
      extractKChoice (finiteNeighbourhoodProfile H e u) k =
        extractKChoice (finiteNeighbourhoodProfile H e v) k :=
    huChoice.trans hv.2.symm
  exact (hInjective huOutside hv.1 hEqualChoices).symm

end EPPAIII.CliqueCovers
