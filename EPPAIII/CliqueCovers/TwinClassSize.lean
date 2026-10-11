import EPPAIII.CliqueCovers.TwinClassTransport

/-!
# Size and distinctness bounds for selected true-twin classes

Under zero partial outside profiles, every base clique C_i lies
within a single class of the closed-neighbourhood equivalence,
and that class has at least t vertices. Independently of the
zero-partial assumption, distinct selected cliques give distinct
classes, because a twin class is a clique.

Together with the transitive equal-class-size theorem, these are
the finite counting inputs for the true-twin quotient reduction.
-/

namespace EPPAIII.CliqueCovers

/-- A selected base clique embeds into the closed twin class of
each one of its vertices, so its class has at least t points. -/
theorem selected_clique_card_le_twin_class {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = t)
    (i : Fin s) (a : Fin t) :
    t ≤ (closedTwinClass H (e (i,a))).card := by
  classical
  let image : Finset W :=
    (Finset.univ : Finset (Fin t)).image (fun b => e (i,b))
  have hinj : Function.Injective (fun b : Fin t => e (i,b)) := by
    intro b c h
    exact congrArg Prod.snd (e.injective h)
  have hImage : image.card = t := by
    unfold image
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hSubset : image ⊆ closedTwinClass H (e (i,a)) := by
    intro w hw
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hw
    have hSame :=
      selected_clique_same_closed_neighbourhood
        H e he hNoPartial i a b
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSame⟩
  calc
    t = image.card := hImage.symm
    _ ≤ (closedTwinClass H (e (i,a))).card :=
      Finset.card_le_card hSubset

/-- The canonical twin class of each selected clique is distinct.
An anchor inside each clique suffices, and there is no no-partial
assumption here. -/
theorem selected_clique_twin_classes_injective {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (a : Fin t) :
    Function.Injective
      (fun i : Fin s => closedTwinClass H (e (i,a))) := by
  classical
  intro i j hEq
  by_contra hij
  have hSelf : SameClosedNeighbourhood H (e (j,a)) (e (j,a)) := rfl
  have hj : e (j,a) ∈ closedTwinClass H (e (j,a)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSelf⟩
  have hi : e (j,a) ∈ closedTwinClass H (e (i,a)) := by
    rw [hEq]
    exact hj
  have hSame : SameClosedNeighbourhood H (e (i,a)) (e (j,a)) :=
    (Finset.mem_filter.mp hi).2
  exact different_cliques_not_same_closed_neighbourhood
    H e he i j hij a a hSame

end EPPAIII.CliqueCovers
