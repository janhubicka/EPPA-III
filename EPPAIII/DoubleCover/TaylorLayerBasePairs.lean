import EPPAIII.DoubleCover.TaylorTriangleFibres
import EPPAIII.DoubleCover.TaylorTriangleLayerCases
import EPPAIII.DoubleCover.ClusterComponentEdges

/-!
# Taylor triangle layers as genuine finite base-graph sets

For the Taylor inter-fibre matrix, triangles through (false,x)
with two bottom vertices correspond exactly to ordered pairs of
distinct neighbours of x in the clique base graph.

One-bottom/one-top triangles correspond exactly to the mixed
base-pattern set already counted in ClusterMixedTriangleCount.

Two-top triangles correspond exactly to oriented base edges
outside the complete clique component containing x.

The exclusions of base-coordinate coincidences are deductions
from the actual host adjacency and are not added hypotheses.
The optional within-fibre mate edges do not affect these equalities.
-/

namespace EPPAIII.DoubleCover

/-- In a cluster base, bottom-bottom triangles through the
bottom root are precisely pairs of distinct base neighbours. -/
theorem taylor_bottom_bottom_layer_eq_offDiag {V : Type*}
    [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hCluster : BlockSystems.IsClusterGraph G)
    (x : V) :
    taylorTriangleLayerPairs H x false false =
      (clusterBaseNeighbours G x).offDiag := by
  classical
  ext ⟨y,z⟩
  rw [mem_taylorTriangleLayerPairs]
  simp only [Finset.mem_offDiag]
  constructor
  · rintro ⟨hxy,hxz,hyz⟩
    have hXY : G.Adj x y := (he x y).mpr hxy
    have hXZ : G.Adj x z := (he x z).mpr hxz
    have hYZ : G.Adj y z := (he y z).mpr hyz
    exact ⟨by simpa [clusterBaseNeighbours] using hXY,
      by simpa [clusterBaseNeighbours] using hXZ,
      G.ne_of_adj hYZ⟩
  · rintro ⟨hy,hz,hyz⟩
    have hXY : G.Adj x y := by
      simpa [clusterBaseNeighbours] using hy
    have hXZ : G.Adj x z := by
      simpa [clusterBaseNeighbours] using hz
    have hYZ : G.Adj y z :=
      hCluster y x z hXY.symm hXZ hyz
    exact ⟨(he x y).mp hXY, (he x z).mp hXZ,
      (he y z).mp hYZ⟩

/-- The bottom-top layer is exactly the base mixed-triangle
pair set, including the requirement that z is distinct from x. -/
theorem taylor_bottom_top_layer_eq_base_mixed {V : Type*}
    [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (x : V) :
    taylorTriangleLayerPairs H x false true =
      clusterBaseMixedTrianglePairs G x := by
  classical
  ext ⟨y,z⟩
  rw [mem_taylorTriangleLayerPairs]
  simp only [clusterBaseMixedTrianglePairs, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxy,hxz,hyz⟩
    have hzNe : z ≠ x :=
      (taylor_triangle_avoids_root_fibre
        G H he hr x (false,y) (true,z) hxy hxz hyz).2
    have hyzNe : y ≠ z :=
      taylor_triangle_other_fibres_distinct
        G H he hr x (false,y) (true,z) hxy hxz hyz
    obtain ⟨hXY,hnXZ,hnYZ⟩ :=
      (taylor_triangle_bottom_mixed_iff
        G H he hr x y z hzNe.symm hyzNe).mp ⟨hxy,hxz,hyz⟩
    exact ⟨hXY,hzNe,hnXZ,hnYZ⟩
  · rintro ⟨hXY,hzNe,hnXZ,hnYZ⟩
    have hyzNe : y ≠ z := by
      intro hh
      subst z
      exact hnXZ hXY
    exact (taylor_triangle_bottom_mixed_iff
      G H he hr x y z hzNe.symm hyzNe).mpr
        ⟨hXY,hnXZ,hnYZ⟩

/-- Two top-layer vertices form a triangle with the bottom
root exactly when their base coordinates constitute an edge
outside the clique component of x. -/
theorem taylor_top_top_layer_eq_base_outside {V : Type*}
    [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (hCluster : BlockSystems.IsClusterGraph G)
    (x : V) :
    taylorTriangleLayerPairs H x true true =
      clusterBaseTopTopPairs G x := by
  classical
  ext ⟨y,z⟩
  rw [mem_taylorTriangleLayerPairs]
  simp only [clusterBaseTopTopPairs, clusterBaseOrderedEdges,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxy,hxz,hyz⟩
    have hRoot :=
      taylor_triangle_avoids_root_fibre
        G H he hr x (true,y) (true,z) hxy hxz hyz
    have hyzNe : y ≠ z :=
      taylor_triangle_other_fibres_distinct
        G H he hr x (true,y) (true,z) hxy hxz hyz
    obtain ⟨hnXY,_,hYZ⟩ :=
      (taylor_triangle_bottom_top_top_iff G H hr
        x y z hRoot.1.symm hRoot.2.symm hyzNe).mp
          ⟨hxy,hxz,hyz⟩
    refine ⟨hYZ,?_⟩
    intro hy
    rcases (mem_clusterBaseComponent_iff G x y).mp hy with h | h
    · exact hRoot.1 h
    · exact hnXY h
  · rintro ⟨hYZ,hyOut⟩
    have hzOut : z ∉ clusterBaseComponent G x := by
      intro hz
      exact hyOut
        ((clusterBaseComponent_edge_iff G hCluster x y z hYZ).mpr hz)
    have hxyNe : x ≠ y := by
      intro h
      exact hyOut
        ((mem_clusterBaseComponent_iff G x y).mpr (Or.inl h.symm))
    have hxzNe : x ≠ z := by
      intro h
      exact hzOut
        ((mem_clusterBaseComponent_iff G x z).mpr (Or.inl h.symm))
    have hnXY : ¬ G.Adj x y := by
      intro h
      exact hyOut ((mem_clusterBaseComponent_iff G x y).mpr (Or.inr h))
    have hnXZ : ¬ G.Adj x z := by
      intro h
      exact hzOut ((mem_clusterBaseComponent_iff G x z).mpr (Or.inr h))
    exact (taylor_triangle_bottom_top_top_iff
      G H hr x y z hxyNe hxzNe (G.ne_of_adj hYZ)).mpr
        ⟨hnXY,hnXZ,hYZ⟩

end EPPAIII.DoubleCover
