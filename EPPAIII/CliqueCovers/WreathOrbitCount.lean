import EPPAIII.CliqueCovers.ProfileChoices
import EPPAIII.CliqueCovers.WreathChoiceTransitivity

/-!
# The wreath-product profile orbit lower bound

For any profile P ⊆ Fin s × Fin t, let r denote the number of
cliques in which P has exactly k points. An outer permutation moves
those r coordinates to any desired r-element subset R, and inner
permutations choose any k-subset independently at those positions.

This file turns those two verified transitivity lemmas and the
separately verified cardinality of the dependent choice space into
the bound

  choose(s,r) * choose(t,k)^r ≤ |WreathOrbit(P)|.

The proof avoids explicitly constructing an injection: every
parameter choice is *realised* by a profile in the orbit, and
the coordinate extraction map recovers the parameter uniquely.
The induced map from orbit to choices is therefore surjective
onto the whole finite choice space.
-/

namespace EPPAIII.CliqueCovers

noncomputable def wreathTransform {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    Finset (Fin s × Fin t) :=
  (P.map (outerPermutation outer).toEmbedding).map
    (innerPermutation inner).toEmbedding

/-- The collection of profiles obtained by all permutations of
clique indices and independent permutations inside the cliques. -/
noncomputable def wreathOrbit {s t : ℕ}
    (P : Finset (Fin s × Fin t)) :
    Finset (Finset (Fin s × Fin t)) := by
  classical
  exact
    (Finset.univ : Finset
      (Equiv.Perm (Fin s) × (Fin s → Equiv.Perm (Fin t)))).image
      (fun z => wreathTransform P z.1 z.2)

theorem wreathTransform_mem_orbit {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    wreathTransform P outer inner ∈ wreathOrbit P := by
  classical
  unfold wreathOrbit
  exact Finset.mem_image.mpr
    ⟨(outer,inner),Finset.mem_univ _,rfl⟩

/-- Keep only the positions of size-k coordinates and the
corresponding k-subsets. This map is defined for every profile,
even when it has the wrong number of such positions. -/
noncomputable def extractKChoice {s t : ℕ}
    (Q : Finset (Fin s × Fin t)) (k : ℕ) :
    Σ R : Finset (Fin s), ∀ i : Fin s, i ∈ R → Finset (Fin t) :=
  ⟨kPositions Q k, fun i _hi => profileSlice Q i⟩

/-- Inner permutations cannot change which clique indices have
a coordinate of a prescribed cardinality k. -/
theorem kPositions_inner {s t : ℕ}
    (Q : Finset (Fin s × Fin t))
    (inner : Fin s → Equiv.Perm (Fin t))
    (k : ℕ) :
    kPositions
      (Q.map (innerPermutation inner).toEmbedding) k =
        kPositions Q k := by
  classical
  ext i
  rw [mem_kPositions, profileSlice_inner_card]
  exact (mem_kPositions Q k i).symm

/-- Every finite choice of r positions and independent k-subsets
is realised by a profile in the actual wreath-product orbit. -/
theorem wreath_choice_realisable {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (r k : ℕ)
    (hR : (kPositions P k).card = r)
    (choice :
      Σ R : Finset (Fin s), ∀ i : Fin s, i ∈ R → Finset (Fin t))
    (hChoice : choice ∈ profileChoiceSpace s t r k) :
    ∃ Q ∈ wreathOrbit P, extractKChoice Q k = choice := by
  classical
  rcases choice with ⟨R,A⟩
  obtain ⟨hRcard,hAcard⟩ :=
    (mem_profileChoiceSpace_iff s t r k R A).mp hChoice
  obtain ⟨outer,hOuter⟩ :=
    exists_outer_k_positions P k R (hR.trans hRcard.symm)
  let Q₀ : Finset (Fin s × Fin t) :=
    P.map (outerPermutation outer).toEmbedding
  have hQ₀ : kPositions Q₀ k = R := hOuter
  have hQ₀card (i : Fin s) (hi : i ∈ R) :
      (profileSlice Q₀ i).card = k := by
    apply (mem_kPositions Q₀ k i).mp
    rw [hQ₀]
    exact hi
  obtain ⟨inner,hInner⟩ :=
    exists_inner_match_selected Q₀ R k A hQ₀card hAcard
  let Q : Finset (Fin s × Fin t) :=
    Q₀.map (innerPermutation inner).toEmbedding
  have hPositions : kPositions Q k = R := by
    calc
      kPositions Q k = kPositions Q₀ k := kPositions_inner Q₀ inner k
      _ = R := hQ₀
  have hExtract : extractKChoice Q k =
      (⟨R,A⟩ :
        Σ R : Finset (Fin s), ∀ i : Fin s, i ∈ R → Finset (Fin t)) := by
    unfold extractKChoice
    cases hPositions
    congr 1
    funext i hi
    exact hInner i hi
  refine ⟨Q, ?_, hExtract⟩
  exact wreathTransform_mem_orbit P outer inner

/-- General wreath-product orbit-size lower bound, with
no EPPA or outside-clique assumptions. -/
theorem wreath_orbit_card_lower_bound {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (r k : ℕ)
    (hR : (kPositions P k).card = r) :
    (Nat.choose s r) * (Nat.choose t k)^r ≤ (wreathOrbit P).card := by
  classical
  have hSubset :
      profileChoiceSpace s t r k ⊆
        (wreathOrbit P).image (fun Q => extractKChoice Q k) := by
    intro choice hc
    obtain ⟨Q,hQ,hChoice⟩ := wreath_choice_realisable P r k hR choice hc
    exact Finset.mem_image.mpr ⟨Q,hQ,hChoice⟩
  calc
    (Nat.choose s r) * (Nat.choose t k)^r =
        (profileChoiceSpace s t r k).card :=
      (profileChoiceSpace_card s t r k).symm
    _ ≤ ((wreathOrbit P).image (fun Q => extractKChoice Q k)).card :=
      Finset.card_le_card hSubset
    _ ≤ (wreathOrbit P).card := Finset.card_image_le

end EPPAIII.CliqueCovers
