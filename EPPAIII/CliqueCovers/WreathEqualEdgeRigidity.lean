import EPPAIII.CliqueCovers.WreathFourForms
import EPPAIII.CliqueCovers.CliqueUnionDegrees
import EPPAIII.CliqueCovers.RegularEqualEdgeDegree

/-!
# Equal edge counts select sK_t among natural wreath-invariant graphs

For s,t≥2, invariance under the natural S_t wr S_s action forces a
graph on Fin s × Fin t to be one of four forms:
  ⊥, sK_t, (sK_t)ᶜ, ⊤.

Their regular degrees are respectively
  0, t-1, (s-1)*t, st-1.

The three degrees other than t-1 differ strictly from t-1.
The general handshaking identity forces regular graphs with equal
edge counts on the same nonempty vertex set to have equal degrees.
Thus equality with the edge count of sK_t selects sK_t exactly.

This is the final purely graph-theoretic ingredient required for the
one-partial-profile case of Lemma 3.7, once the outside graph is
transported to the canonical wreath action model.
-/

namespace EPPAIII.CliqueCovers

/-- A graph invariant under every natural wreath permutation, with
the same number of edges as sK_t, must be precisely sK_t. -/
theorem wreath_invariant_graph_eq_cliqueUnion_of_edge_count {s t : ℕ}
    (B : SimpleGraph (Fin s × Fin t))
    [DecidableRel B.Adj]
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hInvariant : ∀ (outer : Equiv.Perm (Fin s))
      (inner : Fin s → Equiv.Perm (Fin t)),
      IsGraphAutomorphism B
        ((outerPermutation outer).trans (innerPermutation inner)))
    (hEdges : B.edgeFinset.card =
      (cliqueUnion s t).edgeFinset.card) :
    B = cliqueUnion s t := by
  classical
  have hPos : 0 < Fintype.card (Fin s × Fin t) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos (by omega) (by omega)
  have hGReg : (cliqueUnion s t).IsRegularOfDegree (t - 1) :=
    cliqueUnion_regular (by omega)
  obtain ⟨hDegreePos, hDegreeCross, hDegreeTop⟩ :=
    cliqueUnion_degree_distinct_of_nontrivial s t hs ht
  rcases wreath_invariant_graph_four_forms B hs ht hInvariant with
    hBot | hBase | hCross | hTop
  · have hEdgeBot :
        (cliqueUnion s t).edgeFinset.card =
          (⊥ : SimpleGraph (Fin s × Fin t)).edgeFinset.card := by
      rw [hBot] at hEdges
      exact hEdges.symm
    have hBotReg :
        (⊥ : SimpleGraph (Fin s × Fin t)).IsRegularOfDegree 0 :=
      SimpleGraph.IsRegularOfDegree.bot
    have hDeg :=
      equal_degree_of_regular_equal_edges
        (cliqueUnion s t) (⊥ : SimpleGraph (Fin s × Fin t))
        (t - 1) 0 hPos hGReg hBotReg hEdgeBot
    omega
  · exact hBase
  · have hEdgeCross :
        (cliqueUnion s t).edgeFinset.card =
          ((cliqueUnion s t)ᶜ).edgeFinset.card := by
      rw [hCross] at hEdges
      exact hEdges.symm
    have hCrossReg :=
      cliqueUnion_compl_regular (s := s) (t := t)
    have hDeg :=
      equal_degree_of_regular_equal_edges
        (cliqueUnion s t) ((cliqueUnion s t)ᶜ)
        (t - 1) ((s - 1) * t) hPos hGReg hCrossReg hEdgeCross
    omega
  · have hEdgeTop :
        (cliqueUnion s t).edgeFinset.card =
          (⊤ : SimpleGraph (Fin s × Fin t)).edgeFinset.card := by
      rw [hTop] at hEdges
      exact hEdges.symm
    have hTopReg :
        (⊤ : SimpleGraph (Fin s × Fin t)).IsRegularOfDegree
          (s * t - 1) := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using
        (SimpleGraph.IsRegularOfDegree.top (V := Fin s × Fin t))
    have hDeg :=
      equal_degree_of_regular_equal_edges
        (cliqueUnion s t) (⊤ : SimpleGraph (Fin s × Fin t))
        (t - 1) (s * t - 1) hPos hGReg hTopReg hEdgeTop
    omega

end EPPAIII.CliqueCovers
