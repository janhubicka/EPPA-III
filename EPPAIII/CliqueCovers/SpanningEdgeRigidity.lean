import EPPAIII.CliqueCovers.Basic

/-!
# Equality from spanning clique containment and an exact edge count

The direct Section 3 proof repeatedly constructs a spanning collection
of disjoint cliques in the complementary half B and then invokes
|E(H[B])| = |E(sK_t)| to rule out additional edges.

This elementary graph-theoretic lemma formalizes precisely that last
step: if one finite simple graph contains another as a spanning
subgraph and the two have equal numbers of edges, they are equal.
No vertex transitivity, EPPA, or quotient machinery is used.
-/

namespace EPPAIII.CliqueCovers

/-- Spanning subgraph containment plus equality of finite
edge counts forces equality of the entire simple graphs. -/
theorem graph_eq_of_le_of_edge_card_eq {V : Type*}
    [Fintype V]
    (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hSubgraph : G ≤ H)
    (hEdgeCard : G.edgeFinset.card = H.edgeFinset.card) :
    G = H := by
  classical
  apply SimpleGraph.edgeFinset_inj.mp
  have hSubset : G.edgeFinset ⊆ H.edgeFinset :=
    SimpleGraph.edgeFinset_mono hSubgraph
  exact Finset.eq_of_subset_of_card_le hSubset
    (by rw [hEdgeCard])

/-- Applied to the standard disjoint union sK_t: no additional
edge is possible if its spanning supergraph has the same edge count. -/
theorem cliqueUnion_eq_of_le_of_edge_card_eq (s t : ℕ)
    (H : SimpleGraph (Fin s × Fin t))
    [DecidableRel (cliqueUnion s t).Adj] [DecidableRel H.Adj]
    (hContains : cliqueUnion s t ≤ H)
    (hEdgeCard :
      (cliqueUnion s t).edgeFinset.card = H.edgeFinset.card) :
    H = cliqueUnion s t := by
  exact (graph_eq_of_le_of_edge_card_eq
    (cliqueUnion s t) H hContains hEdgeCard).symm

end EPPAIII.CliqueCovers
