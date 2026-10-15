import EPPAIII.BlockSystems.RookThreeOutsideAction
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges

/-!
# Edge count reduces the actual R3 outside graph to two candidates

An 18-vertex transitive EPPA host has two equally large halves.
Under any genuine equivalence with the outside half, vertex
transitivity forces the two induced graphs to have the same
number of edges. The selected nine-vertex rook graph has 18 edges.

Under the canonical neighbourhood or nonneighbourhood labels,
the outside graph has only four possible invariant forms. Its
18-edge count eliminates the empty and complete forms, leaving
only the rook graph and its complement, both 18-edge graphs.

This is the graph-level step needed between the canonical profile
labels and the final R3 triangle-count obstruction.
-/

namespace EPPAIII.BlockSystems

/-- Exact edge count of the nine-vertex rook graph. -/
theorem rookThreeGraph_edge_count_eighteen :
    rookThreeGraph.edgeSet.ncard = 18 := by
  classical
  have h : rookThreeGraph.edgeFinset.card = 18 := by decide
  simpa only [← SimpleGraph.card_edgeSet,
    Set.fintypeCard_eq_ncard] using h

/-- The full graph on nine vertices has exactly 36 edges. -/
theorem rookNineComplete_edge_count_thirtysix :
    (⊤ : SimpleGraph rookVertex).edgeSet.ncard = 36 := by
  classical
  have h : (⊤ : SimpleGraph rookVertex).edgeFinset.card = 36 := by decide
  simpa only [← SimpleGraph.card_edgeSet,
    Set.fintypeCard_eq_ncard] using h

/-- For an actual transitive 18-vertex EPPA host, a genuine outside
equivalence with canonical rook neighbourhood labels forces the
outside induced graph to be either the rook graph or its complement. -/
theorem rook_canonical_outside_graph_two_forms
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (f : rookVertex ≃ {w : W // w ∈ finiteOutside e})
    (hInjective : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W))
    (hLabels :
      (∀ x, finiteNeighbourhoodProfile H e (f x).val =
        rookOpenNeighbourhood x) ∨
      (∀ x, finiteNeighbourhoodProfile H e (f x).val =
        rookStrictNonneighbours x)) :
    H.comap (fun x => (f x).val) = rookThreeGraph ∨
      H.comap (fun x => (f x).val) = rookThreeGraphᶜ := by
  classical
  let outside : rookVertex → W := fun x => (f x).val
  have hOutside (x : rookVertex) : outside x ∈ finiteOutside e :=
    (f x).property
  have hFour :
      H.comap outside = ⊥ ∨
      H.comap outside = rookThreeGraph ∨
      H.comap outside = rookThreeGraphᶜ ∨
      H.comap outside = ⊤ :=
    rook_canonical_outside_graph_four_forms
      H e heppa outside hOutside hInjective hLabels
  have hSide :
      ((CliqueCovers.outsideInducedGraph H e).comap f).edgeSet.ncard =
        rookThreeGraph.edgeSet.ncard :=
    CliqueCovers.arbitrary_host_outside_edge_count_eq_base
      rookThreeGraph H e heppa.1 f hTrans
  have hEdges : (H.comap outside).edgeSet.ncard =
      rookThreeGraph.edgeSet.ncard := by
    simpa only [outside, CliqueCovers.outsideInducedGraph] using hSide
  have hCount : (H.comap outside).edgeSet.ncard = 18 :=
    hEdges.trans rookThreeGraph_edge_count_eighteen
  rcases hFour with hBot | hRook | hCompl | hTop
  · have hZero : (H.comap outside).edgeSet.ncard = 0 := by
      rw [hBot]
      simp
    omega
  · exact Or.inl hRook
  · exact Or.inr hCompl
  · have hFull : (H.comap outside).edgeSet.ncard = 36 := by
      rw [hTop]
      exact rookNineComplete_edge_count_thirtysix
    omega

end EPPAIII.BlockSystems
