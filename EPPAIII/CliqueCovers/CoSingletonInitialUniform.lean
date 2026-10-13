import EPPAIII.CliqueCovers.EppaOuterRigidity
import EPPAIII.CliqueCovers.UniquePartialSize

/-!
# Uniform other coordinates of a unique co-singleton profile

At a double-sized EPPA witness, saturation of the unique size-(t-1)
coordinate forces all other slices to be either empty or full, and
outer rigidity shows that their status is the same for every other
clique index. No vertex-transitivity or a priori outside partition
is used.
-/

namespace EPPAIII.CliqueCovers

/-- Exactly one co-singleton coordinate forces all remaining
coordinates to share a Boolean complete/empty value. -/
theorem eppa_unique_cosingleton_other_slices_uniform {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1) :
    ∃ (i : Fin s) (b : Bool),
      kPositions (finiteNeighbourhoodProfile H e w) (t - 1) = {i} ∧
      ∀ j : Fin s, j ≠ i →
        profileSlice (finiteNeighbourhoodProfile H e w) j =
          if b then (Finset.univ : Finset (Fin t)) else ∅ := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hUnique
  let i0 : Fin s := ⟨0, by omega⟩
  let i1 : Fin s := ⟨1, by omega⟩
  let j0 : Fin s := if i = i0 then i1 else i0
  have hj0 : j0 ≠ i := by
    dsimp [j0]
    split_ifs with hi0
    · subst i
      intro h
      have hval := congrArg Fin.val h
      simp [i0, i1] at hval
    · exact Ne.symm hi0
  have hj0Not :
      j0 ∉ kPositions (finiteNeighbourhoodProfile H e w) (t - 1) := by
    rw [hi]
    simpa using hj0
  have hTrivial :=
    eppa_unique_partial_size_other_coordinates_trivial
      H e heppa hOrder w hw (t - 1) (by omega)
      (by omega) (by omega) hUnique j0 hj0Not
  have hEqual (j : Fin s) (hj : j ≠ i) :
      profileSlice (finiteNeighbourhoodProfile H e w) j =
        profileSlice (finiteNeighbourhoodProfile H e w) j0 := by
    have hjNot :
        j ∉ kPositions (finiteNeighbourhoodProfile H e w) (t - 1) := by
      rw [hi]
      simpa using hj
    exact eppa_unique_partial_other_slices_equal
      H e heppa hOrder w hw (t - 1) (by omega)
        (by omega) (by omega) hUnique
          j j0 hjNot hj0Not
  rcases hTrivial with hZero | hFull
  · have hEmpty :
        profileSlice (finiteNeighbourhoodProfile H e w) j0 = ∅ :=
      Finset.card_eq_zero.mp hZero
    refine ⟨i, false, hi, ?_⟩
    intro j hj
    simpa [hEmpty] using hEqual j hj
  · have hUniverse :
        profileSlice (finiteNeighbourhoodProfile H e w) j0 =
          (Finset.univ : Finset (Fin t)) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simp [hFull]
    refine ⟨i, true, hi, ?_⟩
    intro j hj
    simpa [hUniverse] using hEqual j hj

end EPPAIII.CliqueCovers
