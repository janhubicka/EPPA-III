import EPPAIII.CliqueCovers.WreathSlices
import EPPAIII.EPPA.ProfileOrbitBound

/-!
# The zero-partial-profile case: selected cliques are true-twin classes

If every outside neighbourhood meets each selected clique either
completely or not at all, the vertices inside every selected clique
are pairwise adjacent true twins in the host.

This establishes the first graph-theoretic bridge needed for the
true-twin quotient proof of Lemma 3.7. No host transitivity or
homogeneity assumption is needed for this preliminary reduction.
-/

namespace EPPAIII.CliqueCovers

/-- Vertices of a selected clique have the same adjacency to any
outside vertex when its clique-coordinate has size zero or t. -/
theorem outside_adj_uniform_of_no_partial {s t : ℕ}
    {W : Type*} (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = t)
    (w : W) (hw : w ∉ Set.range e)
    (i : Fin s) (a b : Fin t) :
    H.Adj w (e (i,a)) ↔ H.Adj w (e (i,b)) := by
  classical
  let S : Finset (Fin t) :=
    profileSlice (finiteNeighbourhoodProfile H e w) i
  have hCard : S.card = 0 ∨ S.card = t := hNoPartial w hw i
  have hEqual : (a ∈ S) ↔ (b ∈ S) := by
    rcases hCard with hZero | hFull
    · have he : S = ∅ := Finset.card_eq_zero.mp hZero
      simp [he]
    · have he : S = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ S)
        rw [hFull]
        simp
      simp [he]
  have hMem (c : Fin t) :
      c ∈ S ↔ H.Adj w (e (i,c)) := by
    simp [S, profileSlice, finiteNeighbourhoodProfile]
  exact (hMem a).symm.trans (hEqual.trans (hMem b))

/-- The host vertices of one selected clique are pairwise true twins:
they are adjacent, and every third vertex is adjacent to either both
or neither. This is the exact input to the eventual true-twin quotient. -/
theorem selected_clique_true_twins_of_no_partial {s t : ℕ}
    {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = t)
    (i : Fin s) (a b : Fin t) (hab : a ≠ b) :
    H.Adj (e (i,a)) (e (i,b)) ∧
      ∀ w : W, w ≠ e (i,a) → w ≠ e (i,b) →
        (H.Adj (e (i,a)) w ↔ H.Adj (e (i,b)) w) := by
  classical
  constructor
  · exact (he (i,a) (i,b)).mp ⟨rfl, hab⟩
  intro w hwa hwb
  by_cases hw : w ∈ Set.range e
  · obtain ⟨⟨j,c⟩,rfl⟩ := hw
    by_cases hij : i = j
    · subst j
      have hac : a ≠ c := by
        intro h
        subst c
        exact hwa rfl
      have hbc : b ≠ c := by
        intro h
        subst c
        exact hwb rfl
      have ha : H.Adj (e (i,a)) (e (i,c)) :=
        (he (i,a) (i,c)).mp ⟨rfl, hac⟩
      have hb : H.Adj (e (i,b)) (e (i,c)) :=
        (he (i,b) (i,c)).mp ⟨rfl, hbc⟩
      exact ⟨fun _ => hb, fun _ => ha⟩
    · constructor
      · intro h
        exact False.elim (hij ((he (i,a) (j,c)).mpr h).1)
      · intro h
        exact False.elim (hij ((he (i,b) (j,c)).mpr h).1)
  · have hOutside :=
      outside_adj_uniform_of_no_partial H e hNoPartial w hw i a b
    exact (H.adj_comm (e (i,a)) w).trans
      (hOutside.trans (H.adj_comm w (e (i,b))))

end EPPAIII.CliqueCovers
