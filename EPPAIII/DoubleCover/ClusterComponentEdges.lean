import EPPAIII.DoubleCover.ClusterMixedTriangleCount

/-!
# Complete clique components and their ordered edge count

In a cluster graph, the closed neighbourhood of a vertex x is one
complete component, and any edge with one endpoint in that component
has both endpoints in it.

Consequently the ordered base edges split into those inside the
distinguished clique and those completely outside. The former
are exactly the off-diagonal pairs of the component, and their
number is m^2-m, where m is the size of the component.

For the Taylor double, the latter class gives the two-top-layer
triangles through (false,x). This file isolates the underlying
finite graph-counting identity without assuming any component sizes.
-/

namespace EPPAIII.DoubleCover

/-- The clique component containing x, represented by its closed
neighbourhood, when the base is a union of cliques. -/
noncomputable def clusterBaseComponent {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) : Finset V :=
  insert x (clusterBaseNeighbours G x)

theorem mem_clusterBaseComponent_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x y : V) :
    y ∈ clusterBaseComponent G x ↔ y = x ∨ G.Adj x y := by
  classical
  simp [clusterBaseComponent, clusterBaseNeighbours]

/-- Every pair of distinct points in the component is adjacent. -/
theorem clusterBaseComponent_complete {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hCluster : BlockSystems.IsClusterGraph G)
    (x y z : V)
    (hy : y ∈ clusterBaseComponent G x)
    (hz : z ∈ clusterBaseComponent G x)
    (hyz : y ≠ z) :
    G.Adj y z := by
  rcases (mem_clusterBaseComponent_iff G x y).mp hy with hyx | hxy
  · subst y
    rcases (mem_clusterBaseComponent_iff G x z).mp hz with hzx | hxz
    · exact False.elim (hyz hzx.symm)
    · exact hxz
  · rcases (mem_clusterBaseComponent_iff G x z).mp hz with hzx | hxz
    · subst z
      exact hxy.symm
    · exact hCluster y x z hxy.symm hxz hyz

/-- An edge starting in the component ends in the same component. -/
theorem clusterBaseComponent_closed_under_edges {V : Type*}
    [Fintype V]
    (G : SimpleGraph V)
    (hCluster : BlockSystems.IsClusterGraph G)
    (x y z : V)
    (hy : y ∈ clusterBaseComponent G x)
    (hyz : G.Adj y z) :
    z ∈ clusterBaseComponent G x := by
  rcases (mem_clusterBaseComponent_iff G x y).mp hy with hyx | hxy
  · subst y
    exact (mem_clusterBaseComponent_iff G x z).mpr (Or.inr hyz)
  · by_cases hxz : x = z
    · exact (mem_clusterBaseComponent_iff G x z).mpr (Or.inl hxz.symm)
    · exact (mem_clusterBaseComponent_iff G x z).mpr
        (Or.inr (hCluster x y z hxy hyz hxz))

/-- Both ends of any base edge lie in the same side of the
distinguished clique-component partition. -/
theorem clusterBaseComponent_edge_iff {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hCluster : BlockSystems.IsClusterGraph G)
    (x y z : V) (hyz : G.Adj y z) :
    y ∈ clusterBaseComponent G x ↔
      z ∈ clusterBaseComponent G x := by
  constructor
  · intro hy
    exact clusterBaseComponent_closed_under_edges
      G hCluster x y z hy hyz
  · intro hz
    exact clusterBaseComponent_closed_under_edges
      G hCluster x z y hz hyz.symm

/-- Every oriented base edge appears exactly once in this set. -/
noncomputable def clusterBaseOrderedEdges {V : Type*}
    [Fintype V] (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact (Finset.univ : Finset (V × V)).filter
    (fun yz => G.Adj yz.1 yz.2)

/-- Oriented edges whose first endpoint lies inside the
distinguished clique component. -/
noncomputable def clusterBaseInternalOrderedEdges {V : Type*}
    [Fintype V] (G : SimpleGraph V) (x : V) : Finset (V × V) := by
  classical
  exact (clusterBaseOrderedEdges G).filter
    (fun yz => yz.1 ∈ clusterBaseComponent G x)

/-- Oriented edges whose first endpoint lies outside the
distinguished clique component. -/
noncomputable def clusterBaseTopTopPairs {V : Type*}
    [Fintype V] (G : SimpleGraph V) (x : V) : Finset (V × V) := by
  classical
  exact (clusterBaseOrderedEdges G).filter
    (fun yz => yz.1 ∉ clusterBaseComponent G x)

/-- The inside oriented edges are exactly the pairs of distinct
vertices of the complete component. -/
theorem clusterBaseInternalOrderedEdges_eq_offDiag
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hCluster : BlockSystems.IsClusterGraph G) (x : V) :
    clusterBaseInternalOrderedEdges G x =
      (clusterBaseComponent G x).offDiag := by
  classical
  ext ⟨y,z⟩
  simp only [clusterBaseInternalOrderedEdges,
    clusterBaseOrderedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_offDiag]
  constructor
  · rintro ⟨hyz,hy⟩
    exact ⟨hy,clusterBaseComponent_closed_under_edges
      G hCluster x y z hy hyz, G.ne_of_adj hyz⟩
  · rintro ⟨hy,hz,hyz⟩
    exact ⟨clusterBaseComponent_complete G hCluster x y z
      hy hz hyz, hy⟩

/-- The ordered edge count splits into the ordered edges inside
the root clique and the complementary ordered edges outside. -/
theorem clusterBaseOrderedEdges_card_split
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hCluster : BlockSystems.IsClusterGraph G) (x : V) :
    (clusterBaseOrderedEdges G).card =
      ((clusterBaseComponent G x).card *
        (clusterBaseComponent G x).card -
        (clusterBaseComponent G x).card) +
      (clusterBaseTopTopPairs G x).card := by
  classical
  have hSplit :
      (clusterBaseInternalOrderedEdges G x).card +
        (clusterBaseTopTopPairs G x).card =
        (clusterBaseOrderedEdges G).card := by
    simpa only [clusterBaseInternalOrderedEdges,
      clusterBaseTopTopPairs] using
      (Finset.card_filter_add_card_filter_not
        (s := clusterBaseOrderedEdges G)
        (p := fun yz : V × V =>
          yz.1 ∈ clusterBaseComponent G x))
  calc
    (clusterBaseOrderedEdges G).card =
        (clusterBaseInternalOrderedEdges G x).card +
          (clusterBaseTopTopPairs G x).card := hSplit.symm
    _ = ((clusterBaseComponent G x).card *
          (clusterBaseComponent G x).card -
          (clusterBaseComponent G x).card) +
        (clusterBaseTopTopPairs G x).card := by
      rw [clusterBaseInternalOrderedEdges_eq_offDiag G hCluster x,
        Finset.offDiag_card]

end EPPAIII.DoubleCover
