import EPPAIII.DoubleCover.ClusterMixedTriangleCount

/-!
# Complementary neighbour and nonneighbour sets in a finite graph

A finite loopless graph partitions its vertices into the root x,
the neighbours of x, and the strict nonneighbours of x.
The cardinality formula turns the product count of mixed Taylor
triangle patterns into an expression involving only |V| and deg(x).

No vertex transitivity, EPPA, or cluster hypothesis is required for
the partition itself. The mixed-triangle conclusion additionally uses
the cluster property through ClusterMixedTriangleCount.
-/

namespace EPPAIII.DoubleCover

/-- Neighbours and strict nonneighbours, together with the root,
exhaust the finite base vertex set. -/
theorem cluster_base_neighbour_partition {V : Type*} [Fintype V]
    [DecidableEq V]
    (G : SimpleGraph V) (x : V) :
    insert x (clusterBaseNeighbours G x ∪
      clusterBaseStrictNonneighbours G x) = Finset.univ := by
  classical
  ext y
  simp only [Finset.mem_insert, Finset.mem_union,
    Finset.mem_univ, iff_true]
  by_cases hxy : y = x
  · exact Or.inl hxy
  · by_cases hAdj : G.Adj x y
    · right
      left
      simpa [clusterBaseNeighbours] using hAdj
    · right
      right
      simp [clusterBaseStrictNonneighbours, hxy, hAdj]

/-- The two sets in the partition cannot intersect. -/
theorem cluster_base_neighbours_disjoint_non_neighbours
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) :
    Disjoint (clusterBaseNeighbours G x)
      (clusterBaseStrictNonneighbours G x) := by
  classical
  apply Finset.disjoint_left.mpr
  intro y hy hz
  have hAdj : G.Adj x y := by
    simpa [clusterBaseNeighbours] using hy
  have hInfo : y ≠ x ∧ ¬ G.Adj x y := by
    simpa [clusterBaseStrictNonneighbours] using hz
  exact hInfo.2 hAdj

/-- A finite base has n = 1 + degree + strict-nonneighbour count. -/
theorem cluster_base_neighbour_partition_card
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) :
    (clusterBaseNeighbours G x).card +
      (clusterBaseStrictNonneighbours G x).card + 1 =
        Fintype.card V := by
  classical
  let N := clusterBaseNeighbours G x
  let S := clusterBaseStrictNonneighbours G x
  have hDisjoint : Disjoint N S :=
    cluster_base_neighbours_disjoint_non_neighbours G x
  have hNoN : x ∉ N := by
    simp [N, clusterBaseNeighbours]
  have hNoS : x ∉ S := by
    simp [S, clusterBaseStrictNonneighbours]
  have hNoUnion : x ∉ N ∪ S := by
    simpa only [Finset.mem_union, not_or] using
      (And.intro hNoN hNoS)
  have hCover : insert x (N ∪ S) = (Finset.univ : Finset V) :=
    cluster_base_neighbour_partition G x
  change N.card + S.card + 1 = Fintype.card V
  calc
    N.card + S.card + 1 = (N ∪ S).card + 1 := by
      rw [Finset.card_union_of_disjoint hDisjoint]
    _ = (insert x (N ∪ S)).card :=
      (Finset.card_insert_of_notMem hNoUnion).symm
    _ = Fintype.card V := by
      rw [hCover]
      simp

/-- The mixed-layer base-pattern count is degree times the number
of vertices outside the closed neighbourhood of x. -/
theorem cluster_base_mixed_triangle_pairs_card_closed_neighbourhood
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hCluster : BlockSystems.IsClusterGraph G)
    (x : V) :
    (clusterBaseMixedTrianglePairs G x).card =
      (clusterBaseNeighbours G x).card *
        (Fintype.card V - (clusterBaseNeighbours G x).card - 1) := by
  have hPartition := cluster_base_neighbour_partition_card G x
  have hComplement :
      (clusterBaseStrictNonneighbours G x).card =
        Fintype.card V - (clusterBaseNeighbours G x).card - 1 := by
    omega
  rw [cluster_base_mixed_triangle_pairs_card G hCluster x,
    hComplement]

end EPPAIII.DoubleCover
