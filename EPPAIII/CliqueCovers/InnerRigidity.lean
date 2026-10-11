import EPPAIII.CliqueCovers.ProfileSaturation

/-!
# Independent inner moves contradict saturated profile orbits

The usual profile argument only uses that independent inner permutations
inside the cliques of sK_t are genuine automorphisms. If the orbit bound
for the selected size-k coordinates saturates the outside-vertex budget,
then their data determine the full profile. Hence a different coordinate
whose size is strictly between 0 and t is impossible: it can be moved
independently while all selected size-k coordinates remain fixed.

This is the missing group-action step for mixed singleton/co-singleton
profiles, avoiding a full multinomial orbit-size formula.
-/

namespace EPPAIII.CliqueCovers

/-- Any nonempty proper subset of Fin t can be moved by a permutation. -/
theorem proper_subset_has_moving_permutation {t : ℕ}
    (S : Finset (Fin t))
    (hS : 0 < S.card)
    (hProper : S.card < t) :
    ∃ q : Equiv.Perm (Fin t), S.map q.toEmbedding ≠ S := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hS
  have hMissing : ∃ b : Fin t, b ∉ S := by
    by_contra hNo
    push_neg at hNo
    have hAll : S = Finset.univ := by
      ext b
      simp [hNo b]
    have hCard : S.card = t := by simp [hAll]
    omega
  obtain ⟨b,hb⟩ := hMissing
  refine ⟨Equiv.swap a b, ?_⟩
  intro hEq
  have hbMap : b ∈ S.map (Equiv.swap a b).toEmbedding := by
    apply Finset.mem_map.mpr
    exact ⟨a,ha,by simp⟩
  exact hb (hEq ▸ hbMap)

/-- All independent within-clique translates belong to the
concrete wreath-product profile orbit. -/
theorem inner_map_mem_wreath_orbit {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    P.map (innerPermutation inner).toEmbedding ∈ wreathOrbit P := by
  classical
  have h := wreathTransform_mem_orbit P (Equiv.refl _) inner
  simpa [wreathTransform, outerPermutation] using h

/-- The initial profile also belongs to its concrete orbit. -/
theorem self_mem_wreath_orbit {s t : ℕ}
    (P : Finset (Fin s × Fin t)) :
    P ∈ wreathOrbit P := by
  classical
  have h := inner_map_mem_wreath_orbit P (fun _ => Equiv.refl _)
  simpa [innerPermutation] using h

/-- When size-k choice data saturate the orbit cardinality,
every inner permutation that preserves those selected slices
must preserve the entire profile. -/
theorem saturated_profile_inner_rigidity {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (r k : ℕ)
    (hR : (kPositions P k).card = r)
    (hBound : (wreathOrbit P).card ≤
      Nat.choose s r * (Nat.choose t k)^r)
    (inner : Fin s → Equiv.Perm (Fin t))
    (hFix : ∀ i (hi : i ∈ kPositions P k),
      (profileSlice P i).map (inner i).toEmbedding = profileSlice P i) :
    P.map (innerPermutation inner).toEmbedding = P := by
  classical
  let Q : Finset (Fin s × Fin t) :=
    P.map (innerPermutation inner).toEmbedding
  have hPositions : kPositions Q k = kPositions P k :=
    kPositions_inner P inner k
  have hExtract : extractKChoice Q k = extractKChoice P k := by
    unfold extractKChoice
    cases hPositions
    congr 1
    funext i hi
    rw [profileSlice_inner]
    exact hFix i hi
  have hInjective :=
    extractKChoice_injOn_of_orbit_le_choices P r k hR hBound
  exact hInjective
    (inner_map_mem_wreath_orbit P inner)
    (self_mem_wreath_orbit P) hExtract

/-- A profile with a saturated size-k coordinate-choice count
cannot also have a proper nonempty coordinate of a different size. -/
theorem saturated_profile_other_coordinate_not_partial {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (r k : ℕ)
    (hR : (kPositions P k).card = r)
    (hBound : (wreathOrbit P).card ≤
      Nat.choose s r * (Nat.choose t k)^r)
    (j : Fin s) (hj : j ∉ kPositions P k) :
    (profileSlice P j).card = 0 ∨
      (profileSlice P j).card = t := by
  classical
  have hLe : (profileSlice P j).card ≤ t := by
    have h := Finset.card_le_univ (profileSlice P j)
    simpa using h
  by_contra hNot
  have hPos : 0 < (profileSlice P j).card := by omega
  have hProper : (profileSlice P j).card < t := by omega
  obtain ⟨q,hMove⟩ :=
    proper_subset_has_moving_permutation (profileSlice P j) hPos hProper
  let inner : Fin s → Equiv.Perm (Fin t) :=
    fun i => if i = j then q else Equiv.refl _
  have hFix : ∀ i (hi : i ∈ kPositions P k),
      (profileSlice P i).map (inner i).toEmbedding = profileSlice P i := by
    intro i hi
    have hij : i ≠ j := by
      intro heq
      apply hj
      simpa [heq] using hi
    simp [inner, hij]
  have hWhole :=
    saturated_profile_inner_rigidity P r k hR hBound inner hFix
  have hSlice := congrArg (fun Q => profileSlice Q j) hWhole
  rw [profileSlice_inner] at hSlice
  have hInnerJ : inner j = q := by simp [inner]
  rw [hInnerJ] at hSlice
  exact hMove hSlice

end EPPAIII.CliqueCovers
