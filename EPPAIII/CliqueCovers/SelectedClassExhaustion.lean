import EPPAIII.CliqueCovers.TwinClassSize

/-!
# Exact twin-class size means each selected clique fills its class

In the zero-partial case the quotient-counting theorem shows the
canonical closed-neighbourhood classes have size exactly t.
Since each selected clique C_i already consists of t vertices lying
inside one class, it must exhaust that class.

Consequently no outside vertex can belong to a selected twin class.
This is the key elementary interface for identifying the complementary
half with the remaining s twin classes.
-/

namespace EPPAIII.CliqueCovers

/-- Once a selected twin class has order t, it is precisely the
corresponding selected clique. -/
theorem selected_clique_fills_exact_twin_class {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (i : Fin s) (a : Fin t)
    (hSize : (closedTwinClass H (e (i,a))).card = t) :
    closedTwinClass H (e (i,a)) =
      (Finset.univ : Finset (Fin t)).image
        (fun b => e (i,b)) := by
  classical
  let image : Finset W :=
    (Finset.univ : Finset (Fin t)).image (fun b => e (i,b))
  have hInj : Function.Injective (fun b : Fin t => e (i,b)) := by
    intro b c h
    exact congrArg Prod.snd (e.injective h)
  have hImageCard : image.card = t := by
    dsimp [image]
    rw [Finset.card_image_of_injective _ hInj]
    simp
  have hSubset : image ⊆ closedTwinClass H (e (i,a)) := by
    intro w hw
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hw
    have hSame :=
      selected_clique_same_closed_neighbourhood
        H e he hNoPartial i a b
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSame⟩
  have hEq : image = closedTwinClass H (e (i,a)) :=
    Finset.eq_of_subset_of_card_le hSubset (by rw [hImageCard, hSize])
  exact hEq.symm

/-- The complement of the distinguished induced copy is disjoint
from every selected closed-neighbourhood class of exact size t. -/
theorem outside_not_in_exact_selected_twin_class {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (i : Fin s) (a : Fin t)
    (hSize : (closedTwinClass H (e (i,a))).card = t)
    (w : W) (hw : w ∉ Set.range e) :
    ¬ SameClosedNeighbourhood H (e (i,a)) w := by
  intro hSame
  have hMember : w ∈ closedTwinClass H (e (i,a)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSame⟩
  rw [selected_clique_fills_exact_twin_class
      H e he hNoPartial i a hSize] at hMember
  obtain ⟨b, _, hwb⟩ := Finset.mem_image.mp hMember
  exact hw ⟨(i,b), hwb.symm⟩

end EPPAIII.CliqueCovers
