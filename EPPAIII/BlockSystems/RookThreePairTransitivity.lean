import EPPAIII.BlockSystems.RookThreeSubsetAction
import EPPAIII.BlockSystems.RookThreeSmallSubsetOrbits

/-!
# Ordered edge and nonedge orbits of the rook-graph automorphism group

The 72 explicit row/column/transpose automorphisms of R3 act
transitively on oriented edges and independently on oriented
nonedges. We certify those two finite action statements directly
in Lean, using the genuine automorphisms already verified.

Consequently any graph on the same nine vertices whose adjacency
is preserved by all these rook automorphisms has one constant
adjacency bit on the R3 edges, and another on the R3 nonedges.

This is the group-action input for classifying the *actual* outside
half of an R3 EPPA witness after canonical profile indexing.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Any ordered R3 edge can be obtained from one fixed rook edge
by one of the 72 genuine automorphisms. -/
theorem rook_ordered_edge_pair_transitive :
    ∀ u v : rookVertex, rookThreeGraph.Adj u v →
      ∃ p : rookAutParameter,
        rookParameterizedAut p (0,0) = u ∧
        rookParameterizedAut p (0,1) = v := by
  decide

/-- Any ordered R3 nonedge on distinct vertices is the image
of one fixed ordered nonedge under a genuine rook automorphism. -/
theorem rook_ordered_nonedge_pair_transitive :
    ∀ u v : rookVertex, u ≠ v → ¬ rookThreeGraph.Adj u v →
      ∃ p : rookAutParameter,
        rookParameterizedAut p (0,0) = u ∧
        rookParameterizedAut p (1,1) = v := by
  decide

/-- All R3 edges receive the same adjacency value in any graph
invariant under the full explicit rook automorphism subgroup. -/
theorem rook_invariant_graph_edge_value
    (K : SimpleGraph rookVertex)
    (hInvariant : ∀ p : rookAutParameter,
      IsGraphAutomorphism K (rookParameterizedAut p))
    (u v : rookVertex) (hAdj : rookThreeGraph.Adj u v) :
    K.Adj u v ↔ K.Adj (0,0) (0,1) := by
  obtain ⟨p,hu,hv⟩ :=
    rook_ordered_edge_pair_transitive u v hAdj
  simpa only [hu,hv] using
    ((hInvariant p) (0,0) (0,1)).symm

/-- All R3 nonedges receive the same adjacency value in any graph
invariant under the explicit rook automorphism subgroup. -/
theorem rook_invariant_graph_nonedge_value
    (K : SimpleGraph rookVertex)
    (hInvariant : ∀ p : rookAutParameter,
      IsGraphAutomorphism K (rookParameterizedAut p))
    (u v : rookVertex) (huv : u ≠ v)
    (hNonadj : ¬ rookThreeGraph.Adj u v) :
    K.Adj u v ↔ K.Adj (0,0) (1,1) := by
  obtain ⟨p,hu,hv⟩ :=
    rook_ordered_nonedge_pair_transitive u v huv hNonadj
  simpa only [hu,hv] using
    ((hInvariant p) (0,0) (1,1)).symm

end EPPAIII.BlockSystems
