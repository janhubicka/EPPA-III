import EPPAIII.CliqueCovers.InnerRigidity

/-!
# Outer rigidity when one coordinate-choice orbit saturates the budget

The verified saturation theorem says that chosen size-k coordinate
positions and subsets determine the full profile whenever their
parameter-space count exhausts its wreath orbit.

An outer permutation that fixes all selected size-k indices fixes
their subsets and positions. Consequently it must fix the complete
profile. Swapping two indices outside those positions now forces
their profile slices to be equal.

This replaces the extra binomial factor choose(s-1,r) from the
one-partial-coordinate case of Lemma 3.7, without proving an exact
multinomial orbit formula.
-/

namespace EPPAIII.CliqueCovers

/-- Outer permutations give genuine members of the wreath orbit. -/
theorem outer_map_mem_wreath_orbit {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (outer : Equiv.Perm (Fin s)) :
    P.map (outerPermutation outer).toEmbedding ∈ wreathOrbit P := by
  classical
  have h :=
    wreathTransform_mem_orbit P outer (fun _ => Equiv.refl _)
  have hId :
      (innerPermutation (fun _ : Fin s => Equiv.refl (Fin t))).toEmbedding =
        Function.Embedding.refl (Fin s × Fin t) := by
    apply Function.Embedding.ext
    rintro ⟨i, a⟩
    rfl
  change
    (P.map (outerPermutation outer).toEmbedding).map
      (innerPermutation (fun _ : Fin s => Equiv.refl (Fin t))).toEmbedding
        ∈ wreathOrbit P at h
  rw [hId, Finset.map_refl] at h
  exact h

/-- The size-k coordinate-position set transforms by outer relabelling. -/
theorem kPositions_outer_map {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (outer : Equiv.Perm (Fin s)) (k : ℕ) :
    kPositions (P.map (outerPermutation outer).toEmbedding) k =
      (kPositions P k).map outer.toEmbedding := by
  classical
  ext i
  rw [mem_kPositions, profileSlice_outer_card]
  constructor
  · intro hi
    exact Finset.mem_map.mpr
      ⟨outer.symm i, (mem_kPositions P k _).mpr hi, by simp⟩
  · intro hi
    obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hi
    have hjEq : j = outer.symm i := by
      apply outer.injective
      simpa using hji
    simpa [← hjEq] using (mem_kPositions P k j).mp hj

/-- If an outer permutation fixes every selected size-k coordinate,
its induced orbit profile has the same extracted coordinate data. -/
theorem extractKChoice_outer_fixed {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (k : ℕ)
    (outer : Equiv.Perm (Fin s))
    (hFix : ∀ i (hi : i ∈ kPositions P k), outer i = i) :
    extractKChoice (P.map (outerPermutation outer).toEmbedding) k =
      extractKChoice P k := by
  classical
  let Q : Finset (Fin s × Fin t) :=
    P.map (outerPermutation outer).toEmbedding
  have hPositions : kPositions Q k = kPositions P k := by
    rw [kPositions_outer_map]
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp hi
      have hjEq : j = i := by simpa [hFix j hj] using hji
      simpa [hjEq] using hj
    · intro hi
      exact Finset.mem_map.mpr ⟨i,hi,hFix i hi⟩
  have hFixInv (i : Fin s) (hi : i ∈ kPositions P k) :
      outer.symm i = i := by
    apply outer.injective
    simpa [hFix i hi]
  have hSlices :
      ∀ i (hi : i ∈ kPositions P k),
        profileSlice Q i = profileSlice P i := by
    intro i hi
    rw [profileSlice_outer, hFixInv i hi]
  unfold extractKChoice
  generalize hK : kPositions P k = R at hPositions ⊢
  cases hPositions
  congr 1
  funext i hi
  exact hSlices i (by rw [hK]; exact hi)

/-- At saturation, every outer permutation fixing the size-k
coordinates must fix the full profile. -/
theorem saturated_profile_outer_rigidity {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (r k : ℕ)
    (hR : (kPositions P k).card = r)
    (hBound : (wreathOrbit P).card ≤
      Nat.choose s r * (Nat.choose t k)^r)
    (outer : Equiv.Perm (Fin s))
    (hFix : ∀ i (hi : i ∈ kPositions P k), outer i = i) :
    P.map (outerPermutation outer).toEmbedding = P := by
  classical
  have hInj :=
    extractKChoice_injOn_of_orbit_le_choices P r k hR hBound
  exact hInj
    (outer_map_mem_wreath_orbit P outer)
    (self_mem_wreath_orbit P)
    (extractKChoice_outer_fixed P k outer hFix)

/-- All unselected coordinates have identical complete slices:
otherwise their transposition changes the full profile without
changing the saturated selected-coordinate choice. -/
theorem saturated_profile_other_slices_equal {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (r k : ℕ)
    (hR : (kPositions P k).card = r)
    (hBound : (wreathOrbit P).card ≤
      Nat.choose s r * (Nat.choose t k)^r)
    (i j : Fin s)
    (hi : i ∉ kPositions P k)
    (hj : j ∉ kPositions P k) :
    profileSlice P i = profileSlice P j := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  let swap : Equiv.Perm (Fin s) := Equiv.swap i j
  have hFix : ∀ m (hm : m ∈ kPositions P k), swap m = m := by
    intro m hm
    have hmi : m ≠ i := by
      intro h
      apply hi
      simpa [h] using hm
    have hmj : m ≠ j := by
      intro h
      apply hj
      simpa [h] using hm
    exact Equiv.swap_apply_of_ne_of_ne hmi hmj
  have hWhole :=
    saturated_profile_outer_rigidity P r k hR hBound swap hFix
  have hSlice :=
    congrArg (fun Q : Finset (Fin s × Fin t) => profileSlice Q i) hWhole
  rw [profileSlice_outer] at hSlice
  have hSwap : swap.symm i = j := by
    simp [swap]
  rw [hSwap] at hSlice
  exact hSlice.symm

end EPPAIII.CliqueCovers
