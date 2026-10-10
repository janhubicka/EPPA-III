import EPPAIII.CliqueCovers.WreathSlices

/-!
# Moving distinguished coordinate positions and their subsets

The selected coordinates of size k can be moved to any other
set of equally many clique positions. Afterwards, the k-subsets
at those positions can be chosen arbitrarily via independent
permutations inside the cliques.

All witnesses are actual outer and inner wreath-product automorphisms
already verified in WreathGenerators. The cardinal injection into the
full orbit remains a separate final theorem.
-/

namespace EPPAIII.CliqueCovers

/-- Indices whose profile coordinate has precisely k vertices. -/
noncomputable def kPositions {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (k : ℕ) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter (fun i => (profileSlice P i).card = k)

theorem mem_kPositions {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (k : ℕ) (i : Fin s) :
    i ∈ kPositions P k ↔ (profileSlice P i).card = k := by
  classical
  simp [kPositions]

/-- Any size-r subset of clique indices can become exactly the set
of indices whose coordinate size is k under an outer permutation. -/
theorem exists_outer_k_positions {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (k : ℕ)
    (R : Finset (Fin s))
    (hCard : (kPositions P k).card = R.card) :
    ∃ p : Equiv.Perm (Fin s),
      kPositions (P.map (outerPermutation p).toEmbedding) k = R := by
  classical
  obtain ⟨p,hp⟩ :=
    Equiv.Perm.exists_map_finset_eq (kPositions P k) R hCard
  refine ⟨p, ?_⟩
  ext i
  rw [mem_kPositions, profileSlice_outer]
  have hMem : i ∈ R ↔ p.symm i ∈ kPositions P k := by
    constructor
    · intro hi
      have hi' : i ∈ (kPositions P k).map p.toEmbedding := by
        rw [hp]
        exact hi
      obtain ⟨j,hj,hij⟩ := Finset.mem_map.mp hi'
      have hji : j = p.symm i := by
        apply p.injective
        simpa using hij
      simpa [← hji] using hj
    · intro hi
      rw [← hp]
      exact Finset.mem_map.mpr ⟨p.symm i, hi, by simp⟩
  simpa [mem_kPositions] using hMem.symm

/-- Every chosen family of k-subsets on the selected indices can
be realised by independent inner permutations. The coordinate
sizes outside R are unchanged. -/
theorem exists_inner_match_selected {s t : ℕ}
    (Q : Finset (Fin s × Fin t)) (R : Finset (Fin s))
    (k : ℕ)
    (A : ∀ i : Fin s, i ∈ R → Finset (Fin t))
    (hQ : ∀ i (hi : i ∈ R), (profileSlice Q i).card = k)
    (hA : ∀ i (hi : i ∈ R), (A i hi).card = k) :
    ∃ q : Fin s → Equiv.Perm (Fin t),
      ∀ i (hi : i ∈ R),
        profileSlice (Q.map (innerPermutation q).toEmbedding) i =
          A i hi := by
  classical
  have hExists : ∀ i : Fin s,
      ∃ q : Equiv.Perm (Fin t),
        ∀ hi : i ∈ R,
          (profileSlice Q i).map q.toEmbedding = A i hi := by
    intro i
    by_cases hi : i ∈ R
    · have hEqual : (profileSlice Q i).card = (A i hi).card := by
        rw [hQ i hi, hA i hi]
      obtain ⟨q,hq⟩ :=
        Equiv.Perm.exists_map_finset_eq (profileSlice Q i) (A i hi) hEqual
      refine ⟨q, ?_⟩
      intro hi'
      simpa using hq
    · refine ⟨Equiv.refl _, ?_⟩
      intro hi'
      exact False.elim (hi hi')
  choose q hq using hExists
  refine ⟨q, ?_⟩
  intro i hi
  rw [profileSlice_inner]
  exact hq i hi

end EPPAIII.CliqueCovers
