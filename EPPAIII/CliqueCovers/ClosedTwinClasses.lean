import EPPAIII.CliqueCovers.TrueTwins

/-!
# Closed-neighbourhood equivalence in the zero-partial case

Vertices of one selected clique were shown in TrueTwins.lean to be
adjacent true twins. This module proves that the corresponding closed
neighbourhoods coincide and packages equality of closed neighbourhoods
as a genuine equivalence relation on the host vertices.

Distinct equivalence classes cannot share an edge through the twin
relation; in particular, vertices in distinct base cliques cannot
belong to the same closed-neighbourhood class, since the selected
base graph has no edges between these cliques.

This is the first quotient-level interface for the non-homogeneous
zero-partial-profile case of Lemma 3.7.
-/

namespace EPPAIII.CliqueCovers

def closedNeighbourhood {W : Type*}
    (H : SimpleGraph W) (u : W) : Set W :=
  {w | w = u ∨ H.Adj u w}

/-- Pairwise adjacent true twins have identical closed neighbourhoods. -/
theorem closedNeighbourhood_eq_of_true_twins {W : Type*}
    (H : SimpleGraph W) (u v : W)
    (huv : H.Adj u v)
    (hThird : ∀ w : W, w ≠ u → w ≠ v →
      (H.Adj u w ↔ H.Adj v w)) :
    closedNeighbourhood H u = closedNeighbourhood H v := by
  classical
  ext w
  by_cases hwu : w = u
  · subst w
    simp [closedNeighbourhood, huv.symm]
  by_cases hwv : w = v
  · subst w
    simp [closedNeighbourhood, huv]
  simp only [closedNeighbourhood, Set.mem_setOf_eq, hwu, hwv, false_or]
  exact hThird w hwu hwv

/-- Vertices are equivalent precisely when their closed
neighbourhoods agree. -/
def SameClosedNeighbourhood {W : Type*}
    (H : SimpleGraph W) (u v : W) : Prop :=
  closedNeighbourhood H u = closedNeighbourhood H v

theorem sameClosedNeighbourhood_equivalence {W : Type*}
    (H : SimpleGraph W) : Equivalence (SameClosedNeighbourhood H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rfl
  · intro u v huv
    exact huv.symm
  · intro u v w huv hvw
    exact huv.trans hvw

/-- Any two distinct vertices with equal closed neighbourhoods
are adjacent, so each closed-neighbourhood class is a clique. -/
theorem adjacent_of_same_closed_neighbourhood {W : Type*}
    (H : SimpleGraph W) (u v : W)
    (hDistinct : u ≠ v)
    (hSame : SameClosedNeighbourhood H u v) :
    H.Adj u v := by
  have hv : v ∈ closedNeighbourhood H v := Or.inl rfl
  have hu : v ∈ closedNeighbourhood H u := by
    rw [hSame]
    exact hv
  change v = u ∨ H.Adj u v at hu
  rcases hu with hEq | hAdj
  · exact False.elim (hDistinct hEq.symm)
  · exact hAdj

/-- A whole selected clique lies inside one equivalence class
of closed neighbourhoods when every outside profile is 0/t. -/
theorem selected_clique_same_closed_neighbourhood {s t : ℕ}
    {W : Type*} (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = t)
    (i : Fin s) (a b : Fin t) :
    SameClosedNeighbourhood H (e (i,a)) (e (i,b)) := by
  by_cases hab : a = b
  · subst b
    rfl
  · obtain ⟨hAdj,hThird⟩ :=
      selected_clique_true_twins_of_no_partial H e he hNoPartial i a b hab
    exact closedNeighbourhood_eq_of_true_twins H _ _ hAdj hThird

/-- Distinct selected base cliques belong to distinct
closed-neighbourhood classes (assuming they are nonempty). -/
theorem different_cliques_not_same_closed_neighbourhood {s t : ℕ}
    {W : Type*} (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (i j : Fin s) (hij : i ≠ j)
    (a b : Fin t) :
    ¬ SameClosedNeighbourhood H (e (i,a)) (e (j,b)) := by
  intro hSame
  have hab : e (i,a) ≠ e (j,b) := by
    intro h
    have heq : (i,a) = (j,b) := e.injective h
    exact hij (congrArg Prod.fst heq)
  have hEdge :=
    adjacent_of_same_closed_neighbourhood H _ _ hab hSame
  exact hij ((he (i,a) (j,b)).mpr hEdge).1

end EPPAIII.CliqueCovers
