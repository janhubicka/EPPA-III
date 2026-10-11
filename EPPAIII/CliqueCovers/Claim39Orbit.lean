import EPPAIII.CliqueCovers.WreathOrbitCount
import EPPAIII.CliqueCovers.Claim39Arithmetic
import EPPAIII.CliqueCovers.WreathGenerators

/-!
# The full EPPA profile orbit lower bound for s disjoint t-cliques

This connects the unconditional wreath-profile orbit lower bound to
the *actual* finite automorphism profile orbit of G=sK_t in the host H.

Every outer clique permutation and every independent inner
permutation is already a verified automorphism of sK_t. Their
composition therefore contributes its translated profile to the
EPPA orbit. The previously proved finite-profile transport identity
shows that this translated profile is precisely the corresponding
wreath-transform image of the original neighbourhood profile.

The resulting theorem completes the general k=1 or k=t-1 restriction
on any partial coordinate with no assumption that extensions fix a
complementary clique D_j. It does NOT by itself establish the
two-sided regularity of C_i--D_j blocks (separate issue C14).
-/

namespace EPPAIII.CliqueCovers

/-- A finite translated neighbourhood profile is the image of
the original finite profile under the base permutation. -/
theorem translatedFiniteProfile_eq_map {V W : Type*}
    [Fintype V] (H : SimpleGraph W) (e : V ↪ W)
    (w : W) (p : Equiv.Perm V) :
    translatedFiniteProfile H e w p =
      (finiteNeighbourhoodProfile H e w).map p.toEmbedding := by
  classical
  ext x
  constructor
  · intro hx
    apply Finset.mem_map.mpr
    refine ⟨p.symm x, ?_, ?_⟩
    · simpa [translatedFiniteProfile, finiteNeighbourhoodProfile] using hx
    · simp
  · intro hx
    obtain ⟨a,ha,hpa⟩ := Finset.mem_map.mp hx
    have hEq : a = p.symm x := by
      apply p.injective
      simpa using hpa
    have ha' : H.Adj w (e a) := by
      simpa [finiteNeighbourhoodProfile] using ha
    simpa [translatedFiniteProfile, hEq] using ha'

/-- The outer and independent inner permutations compose to
a genuine automorphism of sK_t. -/
theorem combined_wreath_aut {s t : ℕ}
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    IsGraphAutomorphism (cliqueUnion s t)
      ((outerPermutation outer).trans (innerPermutation inner)) := by
  intro x y
  exact ((outerPermutation_aut outer) x y).trans
    ((innerPermutation_aut inner)
      ((outerPermutation outer) x) ((outerPermutation outer) y))

/-- The concrete wreath transform of a finite profile is exactly
its image under the composed permutation. -/
theorem wreathTransform_eq_map {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    wreathTransform P outer inner =
      P.map (((outerPermutation outer).trans
        (innerPermutation inner)).toEmbedding) := by
  unfold wreathTransform
  rw [Finset.map_map]
  rfl

/-- The generated wreath orbit of an outside neighbourhood
profile is contained in its full Aut(sK_t)-orbit. -/
theorem wreathOrbit_subset_finiteProfileOrbit {s t : ℕ}
    {W : Type*}
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (w : W) :
    wreathOrbit (finiteNeighbourhoodProfile H e w) ⊆
      finiteProfileOrbit (cliqueUnion s t) H e w := by
  classical
  intro Q hQ
  have hWitness :
      ∃ z : Equiv.Perm (Fin s) × (Fin s → Equiv.Perm (Fin t)),
        wreathTransform (finiteNeighbourhoodProfile H e w) z.1 z.2 = Q := by
    simpa only [wreathOrbit, Finset.mem_image,
      Finset.mem_univ, true_and] using hQ
  obtain ⟨⟨outer,inner⟩,hImage⟩ := hWitness
  let p := (outerPermutation outer).trans (innerPermutation inner)
  have hAuto : IsGraphAutomorphism (cliqueUnion s t) p :=
    combined_wreath_aut outer inner
  have hMember :=
    translate_in_finite_profile_orbit
      (cliqueUnion s t) H e w p hAuto
  have hEquals :
      translatedFiniteProfile H e w p =
        wreathTransform (finiteNeighbourhoodProfile H e w) outer inner := by
    rw [translatedFiniteProfile_eq_map,
      wreathTransform_eq_map]
  rw [hEquals] at hMember
  exact hImage ▸ hMember

/-- Full orbit lower bound, now proved for the actual EPPA profile
orbit. This result does not assume EPPA; the base automorphism orbit
is intrinsic to the disjoint clique union. -/
theorem finiteProfileOrbit_lower_bound {s t : ℕ}
    {W : Type*}
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (w : W) (k r : ℕ)
    (hr : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r) :
    (Nat.choose s r) * (Nat.choose t k)^r ≤
      (finiteProfileOrbit (cliqueUnion s t) H e w).card := by
  calc
    (Nat.choose s r) * (Nat.choose t k)^r ≤
        (wreathOrbit (finiteNeighbourhoodProfile H e w)).card :=
      wreath_orbit_card_lower_bound (finiteNeighbourhoodProfile H e w) r k hr
    _ ≤ (finiteProfileOrbit (cliqueUnion s t) H e w).card :=
      Finset.card_le_card (wreathOrbit_subset_finiteProfileOrbit H e w)

/-- A nonempty partial neighbourhood coordinate in a host with
exactly s*t outside vertices is a singleton or co-singleton.

No outside-clique partition, regularity, or vertex-transitivity
of H is used here. This is exactly the corrected profile portion
of Claim 3.9; the rest of Claim 3.9 still needs Claim 3.8 or a
replacement to obtain complete bipartite matching blocks. -/
theorem eppa_clique_union_partial_coordinate_extreme {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (w : W) (hw : w ∉ Set.range e)
    (hOutside : (finiteOutside e).card = s * t)
    (k r : ℕ)
    (hr : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hrpos : 0 < r)
    (hkpos : 0 < k) (hklt : k < t) :
    k = 1 ∨ k + 1 = t := by
  classical
  have hrle : r ≤ s := by
    have hle := Finset.card_le_univ
      (kPositions (finiteNeighbourhoodProfile H e w) k)
    simpa [Fintype.card_fin, hr] using hle
  have hspos : 0 < s := lt_of_lt_of_le hrpos hrle
  have hLow :=
    finiteProfileOrbit_lower_bound H e w k r hr
  have hHigh :=
    finite_profile_orbit_card_le_outside
      (cliqueUnion s t) H e heppa w hw
  have hOrb :
      Nat.choose s r * (Nat.choose t k)^r ≤ s * t := by
    calc
      Nat.choose s r * (Nat.choose t k)^r ≤
          (finiteProfileOrbit (cliqueUnion s t) H e w).card := hLow
      _ ≤ (finiteOutside e).card := hHigh
      _ = s * t := hOutside
  exact only_singleton_or_cosingleton s t r k
    hspos hrpos hrle hkpos hklt hOrb

end EPPAIII.CliqueCovers
