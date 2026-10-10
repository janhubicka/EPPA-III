import EPPAIII.CliqueCovers.WreathGenerators

/-!
# Slices of a neighbourhood profile under wreath-product permutations

A profile is a finite subset of Fin s × Fin t. Its i-th coordinate
is the finite subset of Fin t consisting of points in clique i.

Outer permutations relabel coordinates; inner permutations act
independently on the finite subset at each coordinate. These
formulas are needed to turn the exact combinatorial choice space
into distinct points of the actual profile orbit in Claim 3.9.
-/

namespace EPPAIII.CliqueCovers

noncomputable def profileSlice {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (i : Fin s) : Finset (Fin t) := by
  classical
  exact Finset.univ.filter (fun a => (i,a) ∈ P)

/-- Profile subsets are determined by their family of slices. -/
theorem profile_eq_of_slices {s t : ℕ}
    (P Q : Finset (Fin s × Fin t))
    (h : ∀ i : Fin s, profileSlice P i = profileSlice Q i) :
    P = Q := by
  classical
  ext z
  rcases z with ⟨i,a⟩
  have hEq := congrArg (fun S : Finset (Fin t) => a ∈ S) (h i)
  simpa [profileSlice] using hEq

/-- Relabelling cliques moves the i-th coordinate to p i. -/
theorem profileSlice_outer {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (p : Equiv.Perm (Fin s)) (i : Fin s) :
    profileSlice (P.map (outerPermutation p).toEmbedding) i =
      profileSlice P (p.symm i) := by
  classical
  ext a
  simp only [profileSlice, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_map.mp h
    rcases z with ⟨j,b⟩
    have hij : p j = i := congrArg Prod.fst he
    have hab : b = a := congrArg Prod.snd he
    have hji : j = p.symm i := by
      apply p.injective
      simpa using hij
    simpa [hji,hab] using hz
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨(p.symm i,a), h, ?_⟩
    apply Prod.ext
    · simp [outerPermutation]
    · rfl

/-- Independent within-clique permutations act on each slice. -/
theorem profileSlice_inner {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (p : Fin s → Equiv.Perm (Fin t)) (i : Fin s) :
    profileSlice (P.map (innerPermutation p).toEmbedding) i =
      (profileSlice P i).map (p i).toEmbedding := by
  classical
  ext a
  simp only [profileSlice, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨z,hz,he⟩ := Finset.mem_map.mp h
    rcases z with ⟨j,b⟩
    have hji : j = i := congrArg Prod.fst he
    have hba : p j b = a := congrArg Prod.snd he
    subst j
    apply Finset.mem_map.mpr
    exact ⟨b, by simpa [profileSlice] using hz, hba⟩
  · intro h
    obtain ⟨b,hb,he⟩ := Finset.mem_map.mp h
    apply Finset.mem_map.mpr
    refine ⟨(i,b), ?_, ?_⟩
    · simpa [profileSlice] using hb
    · apply Prod.ext
      · rfl
      · exact he

theorem profileSlice_outer_card {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (p : Equiv.Perm (Fin s)) (i : Fin s) :
    (profileSlice (P.map (outerPermutation p).toEmbedding) i).card =
      (profileSlice P (p.symm i)).card := by
  rw [profileSlice_outer]

theorem profileSlice_inner_card {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (p : Fin s → Equiv.Perm (Fin t)) (i : Fin s) :
    (profileSlice (P.map (innerPermutation p).toEmbedding) i).card =
      (profileSlice P i).card := by
  rw [profileSlice_inner]
  exact Finset.card_map _

end EPPAIII.CliqueCovers
