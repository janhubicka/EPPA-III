import EPPAIII.CliqueCovers.WreathInvariantGraph

/-!
# The four graph types invariant under the natural wreath action

For s,t ≥ 2, a graph on Fin s × Fin t invariant under the whole
natural wreath action of S_t wr S_s has only two Boolean adjacency
parameters: within each block and between distinct blocks.

Consequently the graph is one of
  ⊥,   sK_t,   (sK_t)ᶜ,   ⊤.

This conclusion is independent of EPPA. In the one-partial-coordinate
case of Lemma 3.7 it will be applied to the complementary graph after
transporting the uniquely determined outside action.

The equal-edge-count theorem distinguishing sK_t from the other
three cases remains a separate proof obligation.
-/

namespace EPPAIII.CliqueCovers

/-- Exactly four simple graph patterns can be invariant under the
natural wreath action when there are at least two blocks of size
at least two. -/
theorem wreath_invariant_graph_four_forms {s t : ℕ}
    (B : SimpleGraph (Fin s × Fin t))
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hInvariant : ∀ (outer : Equiv.Perm (Fin s))
      (inner : Fin s → Equiv.Perm (Fin t)),
      IsGraphAutomorphism B
        ((outerPermutation outer).trans (innerPermutation inner))) :
    B = ⊥ ∨ B = cliqueUnion s t ∨
      B = (cliqueUnion s t)ᶜ ∨ B = ⊤ := by
  classical
  obtain ⟨within, between, hAdj⟩ :=
    wreath_invariant_graph_adj_characterization B hs ht hInvariant
  by_cases hWithin : within
  · by_cases hBetween : between
    · right; right; right
      apply SimpleGraph.ext
      funext x y
      apply propext
      change B.Adj x y ↔ x ≠ y
      simpa [hWithin, hBetween] using hAdj x y
    · right; left
      apply SimpleGraph.ext
      funext x y
      apply propext
      rcases x with ⟨i,a⟩
      rcases y with ⟨j,b⟩
      change B.Adj (i,a) (j,b) ↔ (i = j ∧ a ≠ b)
      have h := hAdj (i,a) (j,b)
      by_cases hij : i = j
      · subst j
        simpa [hWithin, hBetween] using h
      · simpa [hWithin, hBetween, hij] using h
  · by_cases hBetween : between
    · right; right; left
      apply SimpleGraph.ext
      funext x y
      apply propext
      rcases x with ⟨i,a⟩
      rcases y with ⟨j,b⟩
      have hCross :
          (cliqueUnion s t)ᶜ.Adj (i,a) (j,b) ↔ i ≠ j := by
        by_cases hij : i = j
        · subst j
          simp [SimpleGraph.compl_adj, cliqueUnion]
        · simp [SimpleGraph.compl_adj, cliqueUnion, hij]
      rw [hCross]
      have h := hAdj (i,a) (j,b)
      by_cases hij : i = j
      · subst j
        simpa [hWithin, hBetween] using h
      · simpa [hWithin, hBetween, hij] using h
    · left
      apply SimpleGraph.ext
      funext x y
      apply propext
      change B.Adj x y ↔ False
      simpa [hWithin, hBetween] using hAdj x y

end EPPAIII.CliqueCovers
