import EPPAIII.CliqueCovers.Claim39OrbitBridge
import EPPAIII.CliqueCovers.ProfileSaturation

/-!
# Saturated profile orbits classify all outside vertices injectively

The EPPA orbit argument previously showed only that the finite
neighbourhood-profile orbit has cardinality at most the number of
outside vertices. Its proof constructs a map into the set of actual
outside profiles; we export that containment here.

When a chosen size-k coordinate count saturates the outside budget,
the orbit is as large as the whole outside half. Therefore every
outside vertex has a distinct profile and all outside profiles lie
in the same finite orbit of Aut(sK_t).

This is the missing bridge from the one-partial profile count to
the canonical, well-defined natural action on the outside half.
No coherent choice of EPPA automorphism lifts is assumed.
-/

namespace EPPAIII.CliqueCovers

/-- Each profile in the EPPA automorphism orbit of an outside
vertex is realised by an actual outside vertex. -/
theorem finite_profile_orbit_subset_outside_image {V W : Type*}
    [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (w : W) (hw : w ∉ Set.range e) :
    finiteProfileOrbit G H e w ⊆
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
  classical
  intro S hS
  obtain ⟨p,hp,hProfile⟩ := Finset.mem_image.mp hS
  have hpAuto : IsGraphAutomorphism G p :=
    (Finset.mem_filter.mp hp).2
  obtain ⟨q,hq,hCompat⟩ :=
    eppa_lifts_total G H e heppa p hpAuto
  have hwOutside : q w ∉ Set.range e :=
    lift_preserves_outside e p q hCompat w hw
  refine Finset.mem_image.mpr ⟨q w, ?_, ?_⟩
  · simpa [finiteOutside] using hwOutside
  · exact (finite_profile_transport H e w p q hCompat hq).trans hProfile

/-- Saturating a parameter-space orbit makes the neighbourhood-profile
map injective on the *entire* complementary half. All those profiles
belong to the single orbit of w. -/
theorem eppa_saturated_outside_profile_bijection {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t) :
    Set.InjOn (finiteNeighbourhoodProfile H e)
      {u | u ∈ finiteOutside e} ∧
    finiteProfileOrbit (cliqueUnion s t) H e w =
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
  classical
  let orbit : Finset (Finset (Fin s × Fin t)) :=
    finiteProfileOrbit (cliqueUnion s t) H e w
  let outside : Finset W := finiteOutside e
  let image : Finset (Finset (Fin s × Fin t)) :=
    outside.image (finiteNeighbourhoodProfile H e)
  have hSubset : orbit ⊆ image :=
    finite_profile_orbit_subset_outside_image
      (cliqueUnion s t) H e heppa w hw
  have hOrbitLower : outside.card ≤ orbit.card := by
    calc
      outside.card = s * t :=
        finiteOutside_card_clique_union e hOrder
      _ = Nat.choose s r * (Nat.choose t k)^r := hSat.symm
      _ ≤ orbit.card := actual_profile_orbit_lower_bound H e w r k hR
  have hImageLower : outside.card ≤ image.card :=
    hOrbitLower.trans (Finset.card_le_card hSubset)
  have hImageUpper : image.card ≤ outside.card :=
    Finset.card_image_le
  have hImageCard : image.card = outside.card :=
    Nat.le_antisymm hImageUpper hImageLower
  have hInjective :
      Set.InjOn (finiteNeighbourhoodProfile H e) {u | u ∈ outside} :=
    Finset.injOn_of_card_image_eq hImageCard
  have hOrbitEq : orbit = image :=
    Finset.eq_of_subset_of_card_le hSubset
      (by rw [hImageCard]; exact hOrbitLower)
  exact ⟨hInjective, hOrbitEq⟩

end EPPAIII.CliqueCovers
