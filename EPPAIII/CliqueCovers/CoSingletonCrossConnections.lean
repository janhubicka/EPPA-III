import EPPAIII.CliqueCovers.CoSingletonCrossOrbit
import EPPAIII.CliqueCovers.CoSingletonTransitiveConclusion

/-!
# Uniform cross-block adjacency in the co-singleton case

The selected coordinate of an outside vertex labelled (i,a) consists
of every point of the i-th clique *except* a; hence diagonal cross
blocks are co-matchings. In all other coordinates, EPPA orbit rigidity
yields a single common complete/empty Boolean cross-block bit.

No prior outside clique partition is assumed. Its identification
as sK_t under vertex transitivity was established separately.
-/

namespace EPPAIII.CliqueCovers

/-- The actual co-singleton outside-profile slices share one Boolean
value away from the omitted-point label's selected coordinate. -/
theorem eppa_cosingleton_cross_slices_uniform {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∃ b : Bool, ∀ (x : Fin s × Fin t) (j : Fin s),
      j ≠ x.1 →
      profileSlice (finiteNeighbourhoodProfile H e
        (saturatedCoSingletonOutsideEquiv
          H e heppa hOrder (by omega) w hw hUnique x).val) j =
        if b then (Finset.univ : Finset (Fin t)) else ∅ := by
  classical
  obtain ⟨i,b,hPositions,hOther⟩ :=
    eppa_unique_cosingleton_other_slices_uniform
      H e heppa hOrder w hw hs ht hUnique
  refine ⟨b, ?_⟩
  intro x j hj
  let label := saturatedCoSingletonOutsideEquiv
    H e heppa hOrder (by omega) w hw hUnique
  let u := label x
  have hChosen := (saturatedCoSingletonOutsideEquiv_slice
    H e heppa hOrder (by omega) w hw hUnique x).1
  have hjNot :
      j ∉ kPositions (finiteNeighbourhoodProfile H e u.val) (t - 1) := by
    rw [hChosen]
    simpa using hj
  exact eppa_saturated_cosingleton_other_slices_uniform
    H e heppa hOrder (by omega) w hw hUnique
    i hPositions b hOther u.val u.property j hjNot

/-- The diagonal cross blocks are co-matchings; all off-diagonal
blocks share one complete/empty adjacency parameter. -/
theorem eppa_cosingleton_cross_adj_uniform {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ∃ b : Bool, ∀ (x : Fin s × Fin t) (j : Fin s)
      (a : Fin t),
      (H.Adj
        (saturatedCoSingletonOutsideEquiv
          H e heppa hOrder (by omega) w hw hUnique x).val
        (e (j,a)) ↔
        if j = x.1 then a ≠ x.2 else b = true) := by
  classical
  obtain ⟨b,hSlices⟩ :=
    eppa_cosingleton_cross_slices_uniform
      H e heppa hOrder w hw hUnique hs ht
  refine ⟨b, ?_⟩
  intro x j a
  let u := saturatedCoSingletonOutsideEquiv
    H e heppa hOrder (by omega) w hw hUnique x
  have hMem :
      H.Adj u.val (e (j,a)) ↔
        a ∈ profileSlice (finiteNeighbourhoodProfile H e u.val) j := by
    simp [profileSlice, finiteNeighbourhoodProfile]
  by_cases hj : j = x.1
  · subst j
    have hDiag :
        profileSlice (finiteNeighbourhoodProfile H e u.val) x.1 =
          (({x.2} : Finset (Fin t))ᶜ) :=
      (saturatedCoSingletonOutsideEquiv_slice
        H e heppa hOrder (by omega) w hw hUnique x).2
    have hMem' : H.Adj u.val (e (x.1,a)) ↔ a ≠ x.2 := by
      rw [hMem, hDiag]
      simp
    simpa [u] using hMem'
  · have hOff :
        profileSlice (finiteNeighbourhoodProfile H e u.val) j =
          if b then (Finset.univ : Finset (Fin t)) else ∅ :=
      hSlices x j hj
    have hMem' : H.Adj u.val (e (j,a)) ↔ b = true := by
      rw [hMem, hOff]
      cases b <;> simp
    simpa [hj, u] using hMem'

end EPPAIII.CliqueCovers
