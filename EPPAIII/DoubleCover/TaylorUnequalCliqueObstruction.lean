import EPPAIII.DoubleCover.TaylorActualTriangleCount
import EPPAIII.DoubleCover.TriangleTransport

/-!
# Unequal cliques and a third component obstruct Taylor transitivity

By the actual graph-level triangle-count formula, ordered
triangles at the bottom vertex over x are counted by
E_oriented + 2 d_x (n-d_x-2), with a common background E.

The difference between the counts at x and y therefore
factors as 2(d_x-d_y)(n-d_x-d_y-2). If x,y lie in
cliques of different sizes and at least one other clique
has a vertex, the counts cannot agree. Vertex transitivity
gives the contradiction.

All numerical facts are now consequences of the verified
adjacency pattern and finite graph counting, not assumptions.
-/

namespace EPPAIII.DoubleCover

theorem taylor_unequal_cliques_three_components_not_transitive
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (hCluster : BlockSystems.IsClusterGraph G)
    (hTrans : BlockSystems.IsVertexTransitive H)
    (x y : V)
    (hDifferent :
      (clusterBaseNeighbours G x).card ≠
        (clusterBaseNeighbours G y).card)
    (hThird :
      (clusterBaseNeighbours G x).card +
        (clusterBaseNeighbours G y).card + 2 <
          Fintype.card V) : False := by
  classical
  let dx : ℤ := ((clusterBaseNeighbours G x).card : ℤ)
  let dy : ℤ := ((clusterBaseNeighbours G y).card : ℤ)
  let n : ℤ := (Fintype.card V : ℤ)
  have hx := taylor_ordered_triangle_count_exact
    G H he hr hCluster x
  have hy := taylor_ordered_triangle_count_exact
    G H he hr hCluster y
  have hNat :
      (orderedTrianglePairsAt H (false,x)).card =
        (orderedTrianglePairsAt H (false,y)).card :=
    orderedTrianglePairsAt_card_transitive
      H hTrans (false,x) (false,y)
  have hCount :
      ((orderedTrianglePairsAt H (false,x)).card : ℤ) =
        ((orderedTrianglePairsAt H (false,y)).card : ℤ) := by
    exact_mod_cast hNat
  have hLocal : dx * (n - dx - 2) =
      dy * (n - dy - 2) := by
    dsimp [dx,dy,n]
    nlinarith [hx, hy, hCount]
  have hFactor :
      (dx - dy) * (n - dx - dy - 2) = 0 := by
    calc
      (dx - dy) * (n - dx - dy - 2) =
          dx * (n - dx - 2) -
            dy * (n - dy - 2) := by ring
      _ = 0 := sub_eq_zero.mpr hLocal
  have hDifferentZ : dx ≠ dy := by
    dsimp [dx,dy]
    exact_mod_cast hDifferent
  have hThirdZ : dx + dy + 2 < n := by
    dsimp [dx,dy,n]
    exact_mod_cast hThird
  rcases mul_eq_zero.mp hFactor with hd | hr
  · exact hDifferentZ (sub_eq_zero.mp hd)
  · have hPos : 0 < n - dx - dy - 2 := by omega
    exact (ne_of_gt hPos) hr

end EPPAIII.DoubleCover
