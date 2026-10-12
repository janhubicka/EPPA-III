import EPPAIII.CliqueCovers.TwinQuotientGraph
import EPPAIII.CliqueCovers.TwinQuotientAdjacency
import EPPAIII.BlockSystems.ClusterObstructions

/-!
# A non-cluster graph has an edge between distinct true-twin classes

The proof of Lemma 3.7 in the zero-partial case needs the canonical
closed-neighbourhood quotient to have positive degree. Rather than
assuming this silently, here is the short direct obstruction:
if every edge had endpoints in one closed-neighbourhood class, then
adjacency would be transitive along induced paths, so the original
graph would be a disjoint union of cliques.

Thus a non-cluster host necessarily has two adjacent vertices with
different closed neighbourhoods, furnishing an edge of the quotient.

The IsClusterGraph predicate is the same as the one used in
EPPAIII.BlockSystems.ClusterObstructions.
-/

namespace EPPAIII.CliqueCovers

/-- In a non-cluster graph, some edge joins two distinct
closed-neighbourhood classes. -/
theorem noncluster_has_edge_between_twin_classes {W : Type*}
    (H : SimpleGraph W)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    ∃ u v : W, H.Adj u v ∧
      ¬ SameClosedNeighbourhood H u v := by
  by_contra hNo
  have hEveryEdgeTwin (u v : W) (huv : H.Adj u v) :
      SameClosedNeighbourhood H u v := by
    by_contra hNot
    exact hNo ⟨u, v, huv, hNot⟩
  apply hNonCluster
  intro a b c hab hbc hac
  have hSame := hEveryEdgeTwin a b hab
  exact
    (adj_iff_of_same_closed_neighbourhood_left
      H a b c hSame hac (H.ne_of_adj hbc)).mpr hbc

/-- The canonical true-twin quotient of a non-cluster graph
has a genuine edge. In particular, its degree is positive
whenever the quotient action is transitive. -/
theorem noncluster_twin_quotient_has_edge {W : Type*}
    (H : SimpleGraph W)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    ∃ x y : ClosedTwinQuotient H,
      (closedTwinQuotientGraph H).Adj x y := by
  obtain ⟨u, v, huv, hDifferent⟩ :=
    noncluster_has_edge_between_twin_classes H hNonCluster
  refine ⟨Quotient.mk (closedTwinSetoid H) u,
          Quotient.mk (closedTwinSetoid H) v, ?_⟩
  exact (closedTwinQuotient_adj_mk H u v).mpr
    ⟨hDifferent, huv⟩

end EPPAIII.CliqueCovers
