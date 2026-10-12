import EPPAIII.CliqueCovers.SingletonInitialUniform

/-!
# Uniform cross-block adjacency in the singleton one-partial case

EPPA saturation makes all outside profiles wreath translates of one
profile. The unique partial singleton coordinate is canonically
labelled by (i,a). EPPA rigidity forces every other coordinate of
the seed profile to be either all empty or all full, with one shared
Boolean choice. Consequently every cross-block adjacency is determined
by the diagonal matching and a single off-diagonal Boolean bit.

This proof never assumes an outside clique partition; that partition
was independently derived from transitivity in the prior module.
-/

namespace EPPAIII.CliqueCovers

/-- Uniform off-diagonal slices of ALL outside vertices when labelled
canonically by their singleton partial coordinate. -/
theorem eppa_singleton_cross_slices_uniform {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∃ b : Bool, ∀ (x : Fin s × Fin t) (j : Fin s),
      j ≠ x.1 →
      profileSlice (finiteNeighbourhoodProfile H e
        (saturatedSingletonOutsideEquiv
          H e heppa hOrder w hw hUnique x).val) j =
        if b then (Finset.univ : Finset (Fin t)) else ∅ := by
  classical
  obtain ⟨i,b,hPositions,hOther⟩ :=
    eppa_unique_singleton_other_slices_uniform
      H e heppa hOrder w hw hs ht hUnique
  refine ⟨b, ?_⟩
  intro x j hj
  let label := saturatedSingletonOutsideEquiv
    H e heppa hOrder w hw hUnique
  let u := label x
  have hChosen := (saturatedSingletonOutsideEquiv_slice
    H e heppa hOrder w hw hUnique x).1
  have hjNot : j ∉ kPositions (finiteNeighbourhoodProfile H e u.val) 1 := by
    rw [hChosen]
    simpa using hj
  exact eppa_saturated_singleton_other_slices_uniform
    H e heppa hOrder w hw hUnique i hPositions b hOther
      u.val u.property j hjNot

/-- Under canonical singleton labels all diagonal cross blocks
are literal matchings, and all off-diagonal blocks have one common
complete/empty status. -/
theorem eppa_singleton_cross_adj_uniform {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∃ b : Bool, ∀ (x : Fin s × Fin t) (j : Fin s)
      (a : Fin t),
      (H.Adj
        (saturatedSingletonOutsideEquiv
          H e heppa hOrder w hw hUnique x).val
        (e (j,a)) ↔
        if j = x.1 then a = x.2 else b = true) := by
  classical
  obtain ⟨b,hSlices⟩ :=
    eppa_singleton_cross_slices_uniform
      H e heppa hOrder w hw hUnique hs ht
  refine ⟨b, ?_⟩
  intro x j a
  let u := saturatedSingletonOutsideEquiv
    H e heppa hOrder w hw hUnique x
  have hMem :
      H.Adj u.val (e (j,a)) ↔
        a ∈ profileSlice (finiteNeighbourhoodProfile H e u.val) j := by
    simp [profileSlice, finiteNeighbourhoodProfile]
  by_cases hj : j = x.1
  · subst j
    have hDiag :=
      (saturatedSingletonOutsideEquiv_slice
        H e heppa hOrder w hw hUnique x).2
    simpa [hDiag] using hMem
  · have hOff := hSlices x j hj
    cases b <;> simpa [hj, hOff] using hMem

end EPPAIII.CliqueCovers
