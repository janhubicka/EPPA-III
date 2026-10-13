import EPPAIII.CliqueCovers.SingletonCrossOrbit
import EPPAIII.CliqueCovers.CoSingletonInitialUniform
import EPPAIII.CliqueCovers.CoSingletonOutsideAction

/-!
# Saturated co-singleton orbits propagate uniform off-diagonal masks

When the only selected size-(t-1) coordinate of a profile is i,
all other coordinates are either empty or full. Every vertex outside
G has a profile in this wreath orbit, so the same complete/empty
Boolean applies away from its own co-singleton coordinate.
-/

namespace EPPAIII.CliqueCovers

/-- At saturation, all actual outside vertices share one complete/empty
off-diagonal status, away from each vertex's unique co-singleton
coordinate. This does not assume vertex-transitivity or an outside
clique decomposition. -/
theorem eppa_saturated_cosingleton_other_slices_uniform {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (ht : 0 < t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (i : Fin s)
    (hPositions :
      kPositions (finiteNeighbourhoodProfile H e w) (t - 1) = {i})
    (b : Bool)
    (hOther : ∀ j : Fin s, j ≠ i →
      profileSlice (finiteNeighbourhoodProfile H e w) j =
        if b then (Finset.univ : Finset (Fin t)) else ∅)
    (u : W) (hu : u ∈ finiteOutside e)
    (j : Fin s)
    (hj : j ∉ kPositions (finiteNeighbourhoodProfile H e u) (t - 1)) :
    profileSlice (finiteNeighbourhoodProfile H e u) j =
      if b then (Finset.univ : Finset (Fin t)) else ∅ := by
  classical
  have hSat :
      Nat.choose s 1 * (Nat.choose t (t - 1))^1 = s * t :=
    coSingletonChoice_saturation s t ht
  have hOrbit :=
    (eppa_saturated_outside_profile_bijection
      H e heppa hOrder w hw 1 (t - 1) hUnique hSat).2 u hu
  rw [← eppa_saturated_wreath_equals_full_orbit
      H e heppa hOrder w hw 1 (t - 1) hUnique hSat] at hOrbit
  unfold wreathOrbit at hOrbit
  obtain ⟨⟨outer,inner⟩,_,hQ⟩ := Finset.mem_image.mp hOrbit
  have hPos :
      kPositions (wreathTransform
        (finiteNeighbourhoodProfile H e w) outer inner) (t - 1) =
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
