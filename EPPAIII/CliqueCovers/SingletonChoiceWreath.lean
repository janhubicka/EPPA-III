import EPPAIII.CliqueCovers.CoSingletonChoiceLabels
import EPPAIII.CliqueCovers.WreathProfileEquivariance

/-!
# The natural wreath action on singleton profile-choice coordinates

A profile whose size-1 positions are exactly {i}, and whose slice
at i is exactly {a}, has extracted combinatorial choice equal to the
canonical label (i,a).  Under an outer/inner wreath transform,
these data become the single position {outer i} with point
inner_(outer i)(a). Consequently the extracted choice transforms
exactly by the natural imprimitive wreath permutation.

This is a pure combinatorial identity. It will be combined with
the already verified finite-profile EPPA lift formula and saturated
outside-choice equivalence to identify the *actual* action on H\G.
-/

namespace EPPAIII.CliqueCovers

/-- A selected singleton position and its singleton slice
determine the complete size-1 extracted choice. -/
theorem extractKChoice_eq_singletonChoice {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (i : Fin s) (a : Fin t)
    (hPositions : kPositions P 1 = {i})
    (hSlice : profileSlice P i = {a}) :
    extractKChoice P 1 = (singletonChoiceOfPair (i,a)).val := by
  classical
  change
    (⟨kPositions P 1, fun j _ => profileSlice P j⟩ :
      Σ R : Finset (Fin s), ∀ j : Fin s, j ∈ R → Finset (Fin t)) =
    ⟨{i}, fun _j _hj => ({a} : Finset (Fin t))⟩
  cases hPositions
  congr 1
  funext j hj
  have hji : j = i := by simpa using hj
  subst j
  exact hSlice

/-- Extraction of size-1 choice data is genuinely equivariant with
the natural S_t wr S_s action on Fin s × Fin t, provided the original
choice has a unique singleton coordinate. -/
theorem extractKChoice_wreath_singleton {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (i : Fin s) (a : Fin t)
    (hPositions : kPositions P 1 = {i})
    (hSlice : profileSlice P i = {a})
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    extractKChoice (wreathTransform P outer inner) 1 =
      (singletonChoiceOfPair
        (((outerPermutation outer).trans
          (innerPermutation inner)) (i,a))).val := by
  classical
  have hPositions' :
      kPositions (wreathTransform P outer inner) 1 = {outer i} := by
    rw [kPositions_wreathTransform, hPositions]
    simp
  have hSlice' :
      profileSlice (wreathTransform P outer inner) (outer i) =
        {(inner (outer i)) a} := by
    rw [profileSlice_wreathTransform]
    simpa [hSlice]
  have hExtract :=
    extractKChoice_eq_singletonChoice
      (wreathTransform P outer inner)
      (outer i) (inner (outer i) a) hPositions' hSlice'
  simpa [outerPermutation, innerPermutation] using hExtract

end EPPAIII.CliqueCovers
