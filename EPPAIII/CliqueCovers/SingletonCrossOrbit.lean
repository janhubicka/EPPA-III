import EPPAIII.CliqueCovers.SingletonTransitiveConclusion
import EPPAIII.CliqueCovers.WreathProfileEquivariance
import EPPAIII.CliqueCovers.OutsideChoiceEquivalence

/-!
# Uniform off-diagonal slices in a saturated singleton orbit

If one profile has a distinguished singleton partial coordinate and
all other slices are uniformly empty or full, all its wreath translates
have the same off-diagonal status. At saturation these are precisely
the actual outside profiles. No outside clique partition is assumed.
-/

namespace EPPAIII.CliqueCovers

theorem wreath_other_slices_uniform {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (i : Fin s) (b : Bool)
    (hOther : ∀ j : Fin s, j ≠ i →
      profileSlice P j =
        if b then (Finset.univ : Finset (Fin t)) else ∅)
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t))
    (j : Fin s) (hj : j ≠ outer i) :
    profileSlice (wreathTransform P outer inner) j =
      if b then (Finset.univ : Finset (Fin t)) else ∅ := by
  classical
  rw [profileSlice_wreathTransform]
  have hDiff : outer.symm j ≠ i := by
    intro h
    apply hj
    have heq := congrArg outer h
    simpa using heq
  rw [hOther (outer.symm j) hDiff]
  cases b <;> simp

/-- Saturation propagates a uniform complete/empty off-diagonal
relation to every actual outside vertex, with the exceptional index
determined by its size-one neighbourhood coordinate. -/
theorem eppa_saturated_singleton_other_slices_uniform {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (i : Fin s)
    (hPositions : kPositions (finiteNeighbourhoodProfile H e w) 1 = {i})
    (b : Bool)
    (hOther : ∀ j : Fin s, j ≠ i →
      profileSlice (finiteNeighbourhoodProfile H e w) j =
        if b then (Finset.univ : Finset (Fin t)) else ∅)
    (u : W) (hu : u ∈ finiteOutside e)
    (j : Fin s)
    (hj : j ∉ kPositions (finiteNeighbourhoodProfile H e u) 1) :
    profileSlice (finiteNeighbourhoodProfile H e u) j =
      if b then (Finset.univ : Finset (Fin t)) else ∅ := by
  classical
  have hSat : Nat.choose s 1 * (Nat.choose t 1)^1 = s * t := by simp
  have hOrbit :=
    (eppa_saturated_outside_profile_bijection
      H e heppa hOrder w hw 1 1 hUnique hSat).2 u hu
  rw [← eppa_saturated_wreath_equals_full_orbit
      H e heppa hOrder w hw 1 1 hUnique hSat] at hOrbit
  unfold wreathOrbit at hOrbit
  obtain ⟨⟨outer,inner⟩,_,hQ⟩ := Finset.mem_image.mp hOrbit
  have hPos :
      kPositions (wreathTransform
        (finiteNeighbourhoodProfile H e w) outer inner) 1 =
        {outer i} := by
    rw [kPositions_wreathTransform, hPositions]
    simp
  have hDiff : j ≠ outer i := by
    intro h
    apply hj
    rw [← hQ, hPos, h]
    simp
  have hUniform := wreath_other_slices_uniform
    (finiteNeighbourhoodProfile H e w)
    i b hOther outer inner j hDiff
  rw [← hQ]
  exact hUniform

end EPPAIII.CliqueCovers
