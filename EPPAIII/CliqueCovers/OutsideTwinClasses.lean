import EPPAIII.CliqueCovers.SelectedClassExhaustion
import EPPAIII.CliqueCovers.SelectedTwinIndependent

/-!
# The complementary half consists of the unselected twin classes

Assume every selected K_t fills its exact size-t closed-neighbourhood
class. Then a host vertex lies outside the distinguished induced copy
if and only if its quotient class is not among the s selected classes.

This is the precise bridge from the quotient-counting theorem to the
claim that the complementary half B is a union of the remaining
true-twin classes. It avoids choosing a labelling of those classes.
-/

namespace EPPAIII.CliqueCovers

/-- No outside vertex belongs to any of the s selected twin classes. -/
theorem outside_quotient_not_selected {s t : ℕ}
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (a : Fin t)
    (hSize : ∀ i : Fin s, (closedTwinClass H (e (i,a))).card = t)
    (w : W) (hw : w ∉ Set.range e) :
    Quotient.mk (closedTwinSetoid H) w ∉
      (selectedTwinClasses H e a : Set (ClosedTwinQuotient H)) := by
  classical
  intro hMem
  change Quotient.mk (closedTwinSetoid H) w ∈
    selectedTwinClasses H e a at hMem
  unfold selectedTwinClasses at hMem
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hMem
  have hSame : SameClosedNeighbourhood H (e (i,a)) w := by
    apply Quotient.exact
    simpa [selectedTwinClassMap] using hi
  exact (outside_not_in_exact_selected_twin_class
    H e he hNoPartial i a (hSize i) w hw) hSame

/-- A vertex whose twin quotient class is not selected
cannot belong to the distinguished base copy. -/
theorem nonselected_quotient_implies_outside {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (a : Fin t) (w : W)
    (hNotSelected : Quotient.mk (closedTwinSetoid H) w ∉
      (selectedTwinClasses H e a : Set (ClosedTwinQuotient H))) :
    w ∉ Set.range e := by
  classical
  intro hw
  obtain ⟨⟨i,b⟩,rfl⟩ := hw
  have hSame :=
    selected_clique_same_closed_neighbourhood
      H e he hNoPartial i a b
  have hQuot :
      Quotient.mk (closedTwinSetoid H) (e (i,a)) =
        Quotient.mk (closedTwinSetoid H) (e (i,b)) :=
    Quotient.sound hSame
  apply hNotSelected
  change Quotient.mk (closedTwinSetoid H) (e (i,b)) ∈
    selectedTwinClasses H e a
  unfold selectedTwinClasses
  exact Finset.mem_image.mpr
    ⟨i, Finset.mem_univ _, by simpa [selectedTwinClassMap] using hQuot⟩

/-- Characterisation of the complementary half solely by
the unselected quotient classes. -/
theorem outside_iff_quotient_not_selected {s t : ℕ}
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (a : Fin t)
    (hSize : ∀ i : Fin s, (closedTwinClass H (e (i,a))).card = t)
    (w : W) :
    w ∉ Set.range e ↔
      Quotient.mk (closedTwinSetoid H) w ∉
        (selectedTwinClasses H e a : Set (ClosedTwinQuotient H)) := by
  constructor
  · exact outside_quotient_not_selected H e he hNoPartial a hSize w
  · exact nonselected_quotient_implies_outside H e he hNoPartial a w

end EPPAIII.CliqueCovers
