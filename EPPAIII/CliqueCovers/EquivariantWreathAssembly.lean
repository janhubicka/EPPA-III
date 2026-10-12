import EPPAIII.CliqueCovers.WreathEqualEdgeRigidity

/-!
# Graph assembly after identifying the natural wreath action

A finite graph on an abstract vertex type U can be transported along
an equivalence with Fin s × Fin t. If every natural base wreath
permutation lifts compatibly to a graph automorphism of the abstract
graph, the transported graph is wreath-invariant. The already
verified four-forms/equal-edge-count rigidity therefore identifies
it exactly with sK_t.

This is the final elementary graph-transport implication in the
one-partial-coordinate branch of Lemma 3.7. Its compatibility
hypothesis must be supplied by the saturated outside-profile choice
parametrization; EPPA alone is *not* silently treated as coherent
wreath equivariance of an arbitrary labelling.
-/

namespace EPPAIII.CliqueCovers

/-- An equivariant labelling of an abstract graph by s clique indices
and t positions, together with the correct edge count, identifies
the graph with the disjoint union of s copies of K_t. -/
theorem graph_eq_cliqueUnion_of_equivariant_wreath_label {s t : ℕ}
    {U : Type*}
    (B : SimpleGraph U)
    (label : (Fin s × Fin t) ≃ U)
    [DecidableRel (B.comap label).Adj]
    [DecidableRel (cliqueUnion s t).Adj]
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hLift : ∀ (outer : Equiv.Perm (Fin s))
      (inner : Fin s → Equiv.Perm (Fin t)),
      ∃ q : Equiv.Perm U,
        IsGraphAutomorphism B q ∧
        ∀ x : Fin s × Fin t,
          q (label x) =
            label (((outerPermutation outer).trans
              (innerPermutation inner)) x))
    (hEdges : (B.comap label).edgeFinset.card =
      (cliqueUnion s t).edgeFinset.card) :
    B.comap label = cliqueUnion s t := by
  apply wreath_invariant_graph_eq_cliqueUnion_of_edge_count
    (B.comap label) hs ht ?_ hEdges
  intro outer inner
  obtain ⟨q, hq, hCompat⟩ := hLift outer inner
  intro x y
  change B.Adj (label x) (label y) ↔
    B.Adj
      (label (((outerPermutation outer).trans
        (innerPermutation inner)) x))
      (label (((outerPermutation outer).trans
        (innerPermutation inner)) y))
  rw [← hCompat x, ← hCompat y]
  exact hq (label x) (label y)

end EPPAIII.CliqueCovers
