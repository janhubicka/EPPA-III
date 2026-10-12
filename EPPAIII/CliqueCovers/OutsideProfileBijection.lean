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

/-- The finite collection of actual neighbourhood profiles of
vertices outside the designated induced copy. The decidability
choice is encapsulated, as for finiteNeighbourhoodProfile itself. -/
noncomputable def finiteOutsideProfileImage {V W : Type*}
    [Fintype V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W) : Finset (Finset V) := by
  classical
  exact (finiteOutside e).image (finiteNeighbourhoodProfile H e)


/-- Each profile in the EPPA automorphism orbit of an outside
vertex is realised by an actual outside vertex. -/
theorem finite_profile_orbit_subset_outside_image {V W : Type*}
    [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (w : W) (hw : w ∉ Set.range e) :
    finiteProfileOrbit G H e w ⊆
      finiteOutsideProfileImage H e := by
  classical
  intro S hS
  change S ∈ (finiteOutside e).image (finiteNeighbourhoodProfile H e)
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
      finiteOutsideProfileImage H e := by
  classical
  let orbit : Finset (Finset (Fin s × Fin t)) :=
    finiteProfileOrbit (cliqueUnion s t) H e w
  let outside : Finset W := finiteOutside e
  let image : Finset (Finset (Fin s × Fin t)) :=
    finiteOutsideProfileImage H e
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
  have hImageUpper : image.card ≤ outside.card := by
    dsimp [image, outside, finiteOutsideProfileImage]
    exact Finset.card_image_le
  have hImageCard : image.card = outside.card :=
    Nat.le_antisymm hImageUpper hImageLower
  have hInjective :
      Set.InjOn (finiteNeighbourhoodProfile H e) {u | u ∈ outside} :=
    Finset.injOn_of_card_image_eq hImageCard
  have hOrbitEq : orbit = image :=
    Finset.eq_of_subset_of_card_le hSubset
      (by rw [hImageCard]; exact hOrbitLower)
  exact ⟨hInjective, hOrbitEq⟩


/-- A single coordinate with proper nonzero neighbourhood size already
saturates the outside profile budget: it must be a singleton or
co-singleton, hence has exactly s*t translated choices.

Therefore all outside vertices have pairwise distinct neighbourhood
profiles and their profiles form precisely one base automorphism orbit. -/
theorem eppa_unique_partial_outside_profiles_bijective {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (k : ℕ) (hs : 0 < s) (hk : 0 < k) (hkt : k < t)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) k).card = 1) :
    Set.InjOn (finiteNeighbourhoodProfile H e)
      {u | u ∈ finiteOutside e} ∧
    finiteProfileOrbit (cliqueUnion s t) H e w =
      finiteOutsideProfileImage H e := by
  classical
  have hPartial :
      0 < (kPositions (finiteNeighbourhoodProfile H e w) k).card := by
    rw [hUnique]
    decide
  have hExtreme : k = 1 ∨ k + 1 = t :=
    eppa_clique_partial_degree_extreme H e heppa
      w hw k hs hk hkt hPartial
      (le_of_eq (finiteOutside_card_clique_union e hOrder))
  have hChoose : Nat.choose t k = t := by
    rcases hExtreme with hOne | hCo
    · simp [hOne]
    · have hComplement : t - k = 1 := by omega
      calc
        Nat.choose t k = Nat.choose t (t - k) :=
          (Nat.choose_symm (Nat.le_of_lt hkt)).symm
        _ = Nat.choose t 1 := by rw [hComplement]
        _ = t := Nat.choose_one_right t
  have hSat : Nat.choose s 1 * (Nat.choose t k)^1 = s * t := by
    simp [hChoose]
  exact eppa_saturated_outside_profile_bijection
    H e heppa hOrder w hw 1 k hUnique hSat

end EPPAIII.CliqueCovers
