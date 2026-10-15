import EPPAIII.DoubleCover.TaylorCountArithmetic

/-!
# Exact triangle counts in the Taylor double of a clique union

The earlier verified graph-level layer equalities identify:
  * bottom-bottom triangles with off-diagonal neighbour pairs;
  * each mixed orientation with the Cartesian mixed base patterns;
  * top-top triangles with oriented base edges outside the
    complete component of the distinguished vertex.

The finite four-layer counting lemma and integer normalization
now give the exact number of ordered triangle pairs at (false,x).
The formula is valid independently of whether optional mate
edges are present, because the actual layer correspondences
exclude all triangles containing such edges.

This is a graph-theoretic theorem, not a numerical assumption.
-/

namespace EPPAIII.DoubleCover

/-- Exact graph-level ordered triangle count in the Taylor double
of a finite disjoint union of cliques. The common background is
the number of ordered base edges. -/
theorem taylor_ordered_triangle_count_exact {V : Type*}
    [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (hCluster : BlockSystems.IsClusterGraph G)
    (x : V) :
    ((orderedTrianglePairsAt H (false,x)).card : ℤ) =
      ((clusterBaseOrderedEdges G).card : ℤ) +
      2 * ((clusterBaseNeighbours G x).card : ℤ) *
        ((Fintype.card V : ℤ) -
          ((clusterBaseNeighbours G x).card : ℤ) - 2) := by
  classical
  let d := (clusterBaseNeighbours G x).card
  let s := (clusterBaseStrictNonneighbours G x).card
  let k := (clusterBaseComponent G x).card
  let t := (clusterBaseTopTopPairs G x).card
  let E := (clusterBaseOrderedEdges G).card
  let T := (orderedTrianglePairsAt H (false,x)).card
  let n := Fintype.card V
  have hLayers : T = (d * d - d) + 2 * (d * s) + t := by
    dsimp [T,d,s,t]
    rw [ordered_triangle_pairs_card_three_layers H x,
      taylor_bottom_bottom_layer_eq_offDiag G H he hCluster x,
      taylor_bottom_top_layer_eq_base_mixed G H he hr x,
      taylor_top_top_layer_eq_base_outside G H he hr hCluster x,
      Finset.offDiag_card,
      cluster_base_mixed_triangle_pairs_card G hCluster x]
  have hEdges : E = (k * k - k) + t := by
    exact clusterBaseOrderedEdges_card_split G hCluster x
  have hComponent : k = d + 1 :=
    clusterBaseComponent_card G x
  have hPartition : n = d + s + 1 :=
    (cluster_base_neighbour_partition_card G x).symm
  exact taylor_ordered_triangle_count_arithmetic
    T E d s k t n hLayers hEdges hComponent hPartition

end EPPAIII.DoubleCover
