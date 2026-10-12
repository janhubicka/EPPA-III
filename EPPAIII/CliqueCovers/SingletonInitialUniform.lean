import EPPAIII.CliqueCovers.SingletonCrossOrbit
import EPPAIII.CliqueCovers.EppaOuterRigidity
import EPPAIII.CliqueCovers.UniquePartialSize

/-!
# One singleton coordinate forces uniform other coordinates

The earlier rigidity theorems prove that when a singleton neighbourhood
coordinate occurs exactly once in a double-sized EPPA witness, every
other coordinate is either empty or full, and all those other slices
are equal. This packages the two facts into one common Boolean value.

No vertex-transitivity, graph regularity, or outside partition is
needed for this conclusion.
-/

namespace EPPAIII.CliqueCovers

theorem eppa_unique_singleton_other_slices_uniform {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1) :
    ∃ (i : Fin s) (b : Bool),
      kPositions (finiteNeighbourhoodProfile H e w) 1 = {i} ∧
      ∀ j : Fin s, j ≠ i →
        profileSlice (finiteNeighbourhoodProfile H e w) j =
          if b then (Finset.univ : Finset (Fin t)) else ∅ := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hUnique
  let i0 : Fin s := ⟨0, by omega⟩
  let i1 : Fin s := ⟨1, by omega⟩
  let j0 : Fin s := if i = i0 then i1 else i0
  have hj0 : j0 ≠ i := by
    dsimp [j0]
    split_ifs with hi0
    · subst i
      intro h
      have hval := congrArg Fin.val h
      simp [i0,i1] at hval
    · exact Ne.symm hi0
  have hj0Not : j0 ∉ kPositions (finiteNeighbourhoodProfile H e w) 1 := by
    rw [hi]
    simpa using hj0
  have hTrivial :=
    eppa_unique_partial_size_other_coordinates_trivial
      H e heppa hOrder w hw 1 (by omega)
      (by decide) (by omega) hUnique j0 hj0Not
  have hEqual (j : Fin s) (hj : j ≠ i) :
      profileSlice (finiteNeighbourhoodProfile H e w) j =
        profileSlice (finiteNeighbourhoodProfile H e w) j0 := by
    have hjNot :
        j ∉ kPositions (finiteNeighbourhoodProfile H e w) 1 := by
      rw [hi]
      simpa using hj
    exact eppa_unique_partial_other_slices_equal
      H e heppa hOrder w hw 1 (by omega)
        (by decide) (by omega) hUnique
          j j0 hjNot hj0Not
  rcases hTrivial with hZero | hFull
  · have hEmpty :
        profileSlice (finiteNeighbourhoodProfile H e w) j0 = ∅ :=
      Finset.card_eq_zero.mp hZero
    refine ⟨i,false,hi,?_⟩
    intro j hj
    simpa [hEmpty] using hEqual j hj
  · have hUniverse :
        profileSlice (finiteNeighbourhoodProfile H e w) j0 =
          (Finset.univ : Finset (Fin t)) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simp [hFull]
    refine ⟨i,true,hi,?_⟩
    intro j hj
    simpa [hUniverse] using hEqual j hj

end EPPAIII.CliqueCovers
