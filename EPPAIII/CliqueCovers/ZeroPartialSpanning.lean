import EPPAIII.CliqueCovers.SpanningEdgeRigidity
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges
import EPPAIII.CliqueCovers.ClosedTwinClasses

/-!
# Zero-partial outside graph from the true-twin fibre labelling

Suppose the outside half has been labelled by s fibres of t vertices,
each fibre lying in a closed-neighbourhood true-twin class. Then each
fibre is a clique. If the host is vertex-transitive, the two equal
halves have equal numbers of edges. Since the selected base is sK_t,
no additional outside edge is possible, and the outside graph equals
sK_t in this particular labelling.

This is the last elementary spanning-subgraph bridge for the
zero-partial case of Lemma 3.7. The actual construction of such a
labelling from the 2s exact true-twin quotient classes is a separate
remaining obligation; we do not hide it inside this theorem.
-/

namespace EPPAIII.CliqueCovers

/-- Equal true-twin classes for each labelled fibre force a
spanning disjoint union of t-cliques in the outside graph. -/
theorem outside_cliqueUnion_le_of_twin_fibre_label {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (label : (Fin s × Fin t) ≃
      {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (a b : Fin t),
      SameClosedNeighbourhood H (label (i,a)).val (label (i,b)).val) :
    cliqueUnion s t ≤ (outsideInducedGraph H e).comap label := by
  intro x y hxy
  rcases x with ⟨i,a⟩
  rcases y with ⟨j,b⟩
  have hCoord : i = j ∧ a ≠ b := hxy
  rcases hCoord with ⟨rfl,hab⟩
  have hne : (label (i,a)).val ≠ (label (i,b)).val := by
    intro h
    have hLabel : label (i,a) = label (i,b) := Subtype.ext h
    have hPair : (i,a) = (i,b) := label.injective hLabel
    exact hab (congrArg Prod.snd hPair)
  change H.Adj (label (i,a)).val (label (i,b)).val
  exact adjacent_of_same_closed_neighbourhood
    H _ _ hne (hFibre i a b)

/-- The labelled outside graph is exactly sK_t, provided each
labelled fibre lies in one closed-twin class. Host transitivity
supplies the crucial equal-half edge count automatically. -/
theorem outside_eq_cliqueUnion_of_transitive_twin_fibres {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hs : 0 < s) (ht : 0 < t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (label : (Fin s × Fin t) ≃
      {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (a b : Fin t),
      SameClosedNeighbourhood H (label (i,a)).val (label (i,b)).val) :
    (outsideInducedGraph H e).comap label = cliqueUnion s t := by
  classical
  letI : Nonempty (Fin s × Fin t) :=
    ⟨(⟨0,hs⟩, ⟨0,ht⟩)⟩
  have hContain :
      cliqueUnion s t ≤ (outsideInducedGraph H e).comap label :=
    outside_cliqueUnion_le_of_twin_fibre_label H e label hFibre
  have hIntrinsic :=
    arbitrary_host_outside_edge_count_eq_base
      (cliqueUnion s t) H e he label hTransitive
  have hEdges :
      (cliqueUnion s t).edgeFinset.card =
        ((outsideInducedGraph H e).comap label).edgeFinset.card := by
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hIntrinsic.symm
  exact cliqueUnion_eq_of_le_of_edge_card_eq
    s t ((outsideInducedGraph H e).comap label) hContain hEdges

end EPPAIII.CliqueCovers
