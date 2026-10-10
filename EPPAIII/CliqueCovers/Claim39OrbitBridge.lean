import EPPAIII.CliqueCovers.WreathOrbitCount
import EPPAIII.CliqueCovers.Claim39Arithmetic
import EPPAIII.CliqueCovers.WreathGenerators
import EPPAIII.EPPA.ProfileOrbitBound

/-!
# Linking the wreath-product orbit to the actual EPPA profile orbit

The independent orbit lower bound for arbitrary s,t,r,k, and the
EPPA profile orbit upper bound, are now both Lean-verified.

This module proves the missing inclusion of the actual wreath orbit
in the profile orbit formed by *all* automorphisms of the selected
graph sK_t. It then derives the extreme degree conclusion:

  if an outside vertex has k neighbours in some selected clique,
  with 0 < k < t and at most s*t outside vertices, then
  k = 1 or k = t-1.

Nothing here assumes the outside vertices decompose into D_j cliques,
or that any EPPA extension fixes any particular D_j. Two-sided
regularity is a separate issue in Claim 3.8.
-/

namespace EPPAIII.CliqueCovers

/-- A translated profile is the image of the original profile under
the base permutation. -/
theorem translatedFiniteProfile_eq_map {V W : Type*}
    [Fintype V] (H : SimpleGraph W) (e : V ↪ W)
    (w : W) (p : Equiv.Perm V) :
    translatedFiniteProfile H e w p =
      (finiteNeighbourhoodProfile H e w).map p.toEmbedding := by
  classical
  ext v
  simp only [translatedFiniteProfile, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    exact Finset.mem_map.mpr
      ⟨p.symm v, by simpa [finiteNeighbourhoodProfile] using h, by simp⟩
  · intro h
    obtain ⟨z,hz,hzv⟩ := Finset.mem_map.mp h
    have hInv : z = p.symm v := by
      apply p.injective
      simpa using hzv
    simpa [hInv, finiteNeighbourhoodProfile] using hz

/-- Any combination of an outer block permutation and independent
inner point permutations is an automorphism of sK_t. -/
theorem wreathPermutation_aut {s t : ℕ}
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    IsGraphAutomorphism (cliqueUnion s t)
      ((outerPermutation outer).trans (innerPermutation inner)) := by
  intro x y
  exact (outerPermutation_aut outer x y).trans
    (innerPermutation_aut inner
      (outerPermutation outer x) (outerPermutation outer y))

/-- Applying the two permutations to a finite subset is equivalent
to applying their composition. -/
theorem wreathTransform_eq_map {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    wreathTransform P outer inner =
      P.map ((outerPermutation outer).trans (innerPermutation inner)).toEmbedding := by
  classical
  ext v
  constructor
  · intro hv
    change v ∈ (P.map (outerPermutation outer).toEmbedding).map
      (innerPermutation inner).toEmbedding at hv
    obtain ⟨u,hu,huv⟩ := Finset.mem_map.mp hv
    obtain ⟨z,hz,hzu⟩ := Finset.mem_map.mp hu
    refine Finset.mem_map.mpr ⟨z,hz,?_⟩
    change innerPermutation inner (outerPermutation outer z) = v
    have hOuter : outerPermutation outer z = u := hzu
    rw [hOuter]
    exact huv
  · intro hv
    obtain ⟨z,hz,hzv⟩ := Finset.mem_map.mp hv
    change v ∈ (P.map (outerPermutation outer).toEmbedding).map
      (innerPermutation inner).toEmbedding
    refine Finset.mem_map.mpr
      ⟨outerPermutation outer z, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨z,hz,rfl⟩
    · exact hzv

/-- The full concrete wreath-product orbit is contained in the
actual finite EPPA profile orbit. This is a group-action statement,
not an assumption about stabilizers of complementary cliques. -/
theorem wreathOrbit_subset_finiteProfileOrbit {s t : ℕ}
    {W : Type*} (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W) (w : W) :
    wreathOrbit (finiteNeighbourhoodProfile H e w) ⊆
      finiteProfileOrbit (cliqueUnion s t) H e w := by
  classical
  intro Q hQ
  obtain ⟨z,_,hZ⟩ := Finset.mem_image.mp
    (show Q ∈ (Finset.univ : Finset
      (Equiv.Perm (Fin s) × (Fin s → Equiv.Perm (Fin t)))).image
        (fun z => wreathTransform (finiteNeighbourhoodProfile H e w) z.1 z.2)
      from hQ)
  rcases z with ⟨outer,inner⟩
  let p : Equiv.Perm (Fin s × Fin t) :=
    (outerPermutation outer).trans (innerPermutation inner)
  have hp : IsGraphAutomorphism (cliqueUnion s t) p :=
    wreathPermutation_aut outer inner
  have hMem := translate_in_finite_profile_orbit
    (cliqueUnion s t) H e w p hp
  have hEq : Q = translatedFiniteProfile H e w p := by
    calc
      Q = wreathTransform (finiteNeighbourhoodProfile H e w)
          outer inner := hZ.symm
      _ = (finiteNeighbourhoodProfile H e w).map p.toEmbedding :=
        wreathTransform_eq_map (finiteNeighbourhoodProfile H e w) outer inner
      _ = translatedFiniteProfile H e w p :=
        (translatedFiniteProfile_eq_map H e w p).symm
  simpa [hEq] using hMem

/-- The wreath-product orbit lower bound is now transferred to the
actual EPPA orbit for arbitrary s,t,r,k. -/
theorem actual_profile_orbit_lower_bound {s t : ℕ}
    {W : Type*} (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W) (w : W)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r) :
    (Nat.choose s r) * (Nat.choose t k)^r ≤
      (finiteProfileOrbit (cliqueUnion s t) H e w).card := by
  calc
    (Nat.choose s r) * (Nat.choose t k)^r ≤
        (wreathOrbit (finiteNeighbourhoodProfile H e w)).card :=
      wreath_orbit_card_lower_bound
        (finiteNeighbourhoodProfile H e w) r k hR
    _ ≤ (finiteProfileOrbit (cliqueUnion s t) H e w).card :=
      Finset.card_le_card (wreathOrbit_subset_finiteProfileOrbit H e w)

/-- **Extreme partial-neighbourhood degrees in Claim 3.9.**

The only outside-size assumption is that the complement of
the distinguished copy has at most s*t vertices. A separate
finite counting lemma can derive this from |H| = 2*s*t.
No regularity of H, no complementary clique partition, and
no assumption that EPPA lifts fix any D_j are needed. -/
theorem eppa_clique_partial_degree_extreme {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (w : W) (hw : w ∉ Set.range e)
    (k : ℕ) (hs : 0 < s) (hk : 0 < k) (hkt : k < t)
    (hPartial : 0 < (kPositions (finiteNeighbourhoodProfile H e w) k).card)
    (hOutside : (finiteOutside e).card ≤ s * t) :
    k = 1 ∨ k + 1 = t := by
  classical
  let r : ℕ :=
    (kPositions (finiteNeighbourhoodProfile H e w) k).card
  have hr : 0 < r := hPartial
  have hrs : r ≤ s := by
    have hCard :
        (kPositions (finiteNeighbourhoodProfile H e w) k).card ≤
        (Finset.univ : Finset (Fin s)).card := Finset.card_le_univ _
    simpa [r] using hCard
  have hLower := actual_profile_orbit_lower_bound
    H e w r k (show
      (kPositions (finiteNeighbourhoodProfile H e w) k).card = r from rfl)
  have hUpper :=
    finite_profile_orbit_card_le_outside
      (cliqueUnion s t) H e heppa w hw
  apply only_singleton_or_cosingleton s t r k hs hr hrs hk hkt
  exact hLower.trans (hUpper.trans hOutside)


/-- Counting the vertices outside the image of a finite embedding.
This makes the orbit theorem applicable directly to a host of order
twice that of the selected graph, rather than requiring an assumed
outside-cardinality inequality. -/
theorem finiteOutside_card_add_base {V W : Type*}
    [Fintype V] [Fintype W] (e : V ↪ W) :
    (finiteOutside e).card + Fintype.card V = Fintype.card W := by
  classical
  have hImage :
      ((Finset.univ : Finset W).filter
        (fun w => w ∈ Set.range e)) =
        (Finset.univ : Finset V).image e := by
    ext w
    simp [Set.mem_range, Finset.mem_image]
  have hPartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset W))
      (p := fun w : W => w ∈ Set.range e)
  rw [hImage] at hPartition
  have hImageCard :
      ((Finset.univ : Finset V).image e).card =
        Fintype.card V := by
    simpa using
      (Finset.card_image_of_injective
        (Finset.univ : Finset V) e.injective)
  rw [hImageCard] at hPartition
  have hBasic :
      Fintype.card V + (finiteOutside e).card =
        Fintype.card W := by
    simpa [finiteOutside] using hPartition
  omega

/-- When the host has twice the size of the selected sK_t, its
complementary vertex set has exactly s*t elements. -/
theorem finiteOutside_card_of_double {s t : ℕ}
    {W : Type*} [Fintype W]
    (e : (Fin s × Fin t) ↪ W)
    (hOrder : Fintype.card W = 2 * s * t) :
    (finiteOutside e).card = s * t := by
  have hCard := finiteOutside_card_add_base e
  have hBase : Fintype.card (Fin s × Fin t) = s * t := by
    simp [Fintype.card_prod]
  have hTotal : Fintype.card W = 2 * (s * t) := by
    calc
      Fintype.card W = 2 * s * t := hOrder
      _ = 2 * (s * t) := by ring
  rw [hBase, hTotal] at hCard
  omega

/-- **Claim 3.9, extreme neighbourhood conclusion for a genuine
double-sized EPPA host.** If some outside vertex has k neighbours
in any selected clique, where 0<k<t, then k=1 or k=t−1.

The step identifying entire cross-block graphs as matchings or
co-matchings remains dependent on Claim 3.8's unverified
two-sided regularity, and is not asserted by this theorem. -/
theorem eppa_clique_degree_extreme_of_double {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (i : Fin s) (k : ℕ) (hs : 0 < s)
    (hk : 0 < k) (hkt : k < t)
    (hSlice : (profileSlice (finiteNeighbourhoodProfile H e w) i).card = k) :
    k = 1 ∨ k + 1 = t := by
  classical
  have hi : i ∈
      kPositions (finiteNeighbourhoodProfile H e w) k :=
    (mem_kPositions _ k i).mpr hSlice
  have hPartial :
      0 < (kPositions (finiteNeighbourhoodProfile H e w) k).card :=
    Finset.card_pos.mpr ⟨i, hi⟩
  exact eppa_clique_partial_degree_extreme H e heppa
    w hw k hs hk hkt hPartial
    (le_of_eq (finiteOutside_card_of_double e hOrder))

end EPPAIII.CliqueCovers
