import EPPAIII.CliqueCovers.OutsideMaskAction
import EPPAIII.CliqueCovers.OutsideTwinIndexBudget

/-!
# The EPPA mask orbit fits into the s outside true-twin classes

For an outside vertex w, every index mask in the Sym(s)-orbit of
its neighbourhood mask is represented by another outside vertex
(OutsideMaskAction). Two outside vertices in the same true-twin
class have the same index mask. Hence choosing one witness for each
orbit mask produces an injective map from the mask orbit into the
set of outside true-twin quotient classes.

When exactly s quotient classes remain outside the designated sK_t,
we therefore have choose(s,|mask(w)|) ≤ s. This closes the missing
graph-level orbit bound, without a coherent system of EPPA lifts,
without choosing outside cliques or even assuming H is transitive
at this point. Transitivity is only used separately to prove the
outside quotient-class budget.
-/

namespace EPPAIII.CliqueCovers

/-- Distinct masks in the orbit of a genuine outside neighbourhood
are witnessed by distinct true-twin quotient classes. -/
theorem eppa_actual_mask_orbit_le_outside_classes {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ u : W, u ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = t)
    (a : Fin t)
    (hSize : ∀ i : Fin s, (closedTwinClass H (e (i,a))).card = t)
    [Fintype (ClosedTwinQuotient H)]
    (w : W) (hw : w ∉ Set.range e) :
    (outerMaskOrbit (outsideIndexMask H e a w)).card ≤
      (outsideTwinQuotientClasses H e a).card := by
  classical
  let S := outerMaskOrbit (outsideIndexMask H e a w)
  let U := outsideTwinQuotientClasses H e a
  have hExists (R : ↥S) :
      ∃ u : W, u ∉ Set.range e ∧ outsideIndexMask H e a u = R.val :=
    eppa_outer_mask_orbit_realized H e heppa a w hw R.val R.property
  let witness (R : ↥S) : W := Classical.choose (hExists R)
  have hWitness (R : ↥S) :
      witness R ∉ Set.range e ∧
        outsideIndexMask H e a (witness R) = R.val :=
    Classical.choose_spec (hExists R)
  let f : ↥S → ↥U := fun R =>
    ⟨Quotient.mk (closedTwinSetoid H) (witness R), by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact outside_quotient_not_selected
        H e heppa.1 hNoPartial a hSize
        (witness R) (hWitness R).1⟩
  have hf : Function.Injective f := by
    intro R T hRT
    have hClass :
        (Quotient.mk (closedTwinSetoid H) (witness R) :
          ClosedTwinQuotient H) =
          Quotient.mk (closedTwinSetoid H) (witness T) :=
      congrArg Subtype.val hRT
    have hSame : SameClosedNeighbourhood H (witness R) (witness T) :=
      Quotient.exact hClass
    have hMask := outsideIndexMask_eq_of_closed_twins
      H e a (witness R) (witness T)
      (hWitness R).1 (hWitness T).1 hSame
    apply Subtype.ext
    calc
      R.val = outsideIndexMask H e a (witness R) :=
        (hWitness R).2.symm
      _ = outsideIndexMask H e a (witness T) := hMask
      _ = T.val := (hWitness T).2
  have hLe : Fintype.card ↥S ≤ Fintype.card ↥U :=
    Fintype.card_le_of_injective f hf
  simpa [S, U, Fintype.card_coe] using hLe

/-- If there are exactly s outside true-twin classes, the
orbit budget forces the index mask of every outside vertex to
have one of four extreme sizes. -/
theorem eppa_actual_mask_card_extreme {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ u : W, u ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = t)
    (a : Fin t)
    (hSize : ∀ i : Fin s, (closedTwinClass H (e (i,a))).card = t)
    [Fintype (ClosedTwinQuotient H)]
    (hBudget : (outsideTwinQuotientClasses H e a).card = s)
    (w : W) (hw : w ∉ Set.range e) :
    (outsideIndexMask H e a w).card = 0 ∨
      (outsideIndexMask H e a w).card = 1 ∨
      (outsideIndexMask H e a w).card + 1 = s ∨
      (outsideIndexMask H e a w).card = s := by
  have hLe := eppa_actual_mask_orbit_le_outside_classes
    H e heppa hNoPartial a hSize w hw
  rw [hBudget] at hLe
  exact outerMaskOrbit_size_extreme (outsideIndexMask H e a w) hLe

end EPPAIII.CliqueCovers
