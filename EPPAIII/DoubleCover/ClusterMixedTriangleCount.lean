import EPPAIII.BlockSystems.ClusterObstructions

/-!
# Cluster graphs: counting mixed Taylor triangle patterns

Fix a base vertex x in a disjoint union of cliques. A mixed-layer
Taylor triangle through (false,x) corresponds to a base edge xy and
a distinct base nonneighbour z, with yz a nonedge. The last condition
follows automatically from the cluster property.

Consequently the ordered mixed-pattern set is a Cartesian product:
the neighbours of x times its distinct nonneighbours. Its cardinality
is the product of their sizes, giving the (k-1)(n-k) term once the
cardinality k of the clique containing x is introduced.

This is a base-graph combinatorial step; transporting the count
through the actual Taylor host remains a separate lemma.
-/

namespace EPPAIII.DoubleCover

/-- Base neighbours of a distinguished vertex. -/
noncomputable def clusterBaseNeighbours {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter (fun y => G.Adj x y)

/-- Base nonneighbours different from the distinguished vertex. -/
noncomputable def clusterBaseStrictNonneighbours {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter
    (fun z => z ≠ x ∧ ¬ G.Adj x z)

/-- Ordered base pairs corresponding to mixed Taylor triangles. -/
noncomputable def clusterBaseMixedTrianglePairs {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) : Finset (V × V) := by
  classical
  exact (Finset.univ : Finset (V × V)).filter
    (fun yz => G.Adj x yz.1 ∧ yz.2 ≠ x ∧
      ¬ G.Adj x yz.2 ∧ ¬ G.Adj yz.1 yz.2)

/-- In a cluster graph, an x-neighbour and a distinct x-nonneighbour
cannot themselves be adjacent. -/
theorem cluster_neighbour_strict_nonneighbour_nonedge {V : Type*}
    (G : SimpleGraph V)
    (hCluster : BlockSystems.IsClusterGraph G)
    (x y z : V) (hxy : G.Adj x y)
    (hzx : z ≠ x) (hnxz : ¬ G.Adj x z) :
    ¬ G.Adj y z := by
  intro hyz
  exact hnxz (hCluster x y z hxy hyz hzx.symm)

/-- The mixed-triangle base patterns are exactly the Cartesian product
of neighbours and distinct nonneighbours of x. -/
theorem cluster_base_mixed_triangle_pairs_eq_product {V : Type*}
    [Fintype V]
    (G : SimpleGraph V)
    (hCluster : BlockSystems.IsClusterGraph G)
    (x : V) :
    clusterBaseMixedTrianglePairs G x =
      (clusterBaseNeighbours G x) ×ˢ
        (clusterBaseStrictNonneighbours G x) := by
  classical
  ext ⟨y,z⟩
  simp only [clusterBaseMixedTrianglePairs, clusterBaseNeighbours,
    clusterBaseStrictNonneighbours, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_product]
  constructor
  · rintro ⟨hxy,hzx,hnxz,_⟩
    exact ⟨hxy,hzx,hnxz⟩
  · rintro ⟨hxy,hzx,hnxz⟩
    exact ⟨hxy,hzx,hnxz,
      cluster_neighbour_strict_nonneighbour_nonedge
        G hCluster x y z hxy hzx hnxz⟩

/-- The mixed-pattern cardinality is a product, not a new
enumeration of triangles or a numerical assumption. -/
theorem cluster_base_mixed_triangle_pairs_card {V : Type*}
    [Fintype V]
    (G : SimpleGraph V)
    (hCluster : BlockSystems.IsClusterGraph G)
    (x : V) :
    (clusterBaseMixedTrianglePairs G x).card =
      (clusterBaseNeighbours G x).card *
        (clusterBaseStrictNonneighbours G x).card := by
  rw [cluster_base_mixed_triangle_pairs_eq_product G hCluster x,
    Finset.card_product]

end EPPAIII.DoubleCover
