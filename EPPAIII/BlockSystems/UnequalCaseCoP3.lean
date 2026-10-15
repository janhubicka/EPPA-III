import EPPAIII.BlockSystems.UnequalThreeComponents

/-!
# Unequal clique sizes already supply an induced co-P3

In a finite cluster graph, vertices of unequal degree belong to
different complete components. At least one of these two components
contains an edge. The endpoints of that edge together with any
vertex of the other component induce the complement of P3.

This removes another artificial hypothesis from the verified
third-component obstruction for unequal cliques. No finite
homogeneous-graph classification is invoked.
-/

namespace EPPAIII.BlockSystems

/-- Every finite union of cliques with two different vertex
degrees contains an induced complement of P3. -/
theorem cluster_unequal_degrees_has_induced_cop3
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hCluster : IsClusterGraph G)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    HasInducedCoP3 G := by
  classical
  obtain ⟨hxy,hnxy⟩ :=
    cluster_unequal_degrees_distinct_nonadjacent
      G hCluster x y hDifferent
  by_cases hxZero : (DoubleCover.clusterBaseNeighbours G x).card = 0
  · have hyPos : 0 < (DoubleCover.clusterBaseNeighbours G y).card := by
      omega
    obtain ⟨z,hz⟩ := Finset.card_pos.mp hyPos
    have hyz : G.Adj y z := by
      simpa [DoubleCover.clusterBaseNeighbours] using hz
    have hxz : ¬ G.Adj x z := by
      intro hxz
      exact hnxy (hCluster x z y hxz hyz.symm hxy)
    have hxNeZ : x ≠ z := by
      intro heq
      subst z
      exact hnxy hyz.symm
    exact ⟨y,x,z,hxy.symm,hxNeZ,G.ne_of_adj hyz,
      (fun h => hnxy h.symm),hxz,hyz⟩
  · have hxPos : 0 < (DoubleCover.clusterBaseNeighbours G x).card := by
      omega
    obtain ⟨z,hz⟩ := Finset.card_pos.mp hxPos
    have hxz : G.Adj x z := by
      simpa [DoubleCover.clusterBaseNeighbours] using hz
    have hyz : ¬ G.Adj y z := by
      intro hyz
      exact hnxy (hCluster x z y hxz hyz.symm hxy)
    have hyNeZ : y ≠ z := by
      intro heq
      subst z
      exact hnxy hxz
    exact ⟨x,y,z,hxy,hyNeZ,G.ne_of_adj hxz,
      hnxy,hyz,hxz⟩

/-- Uniform statement of the repaired unequal-clique obstruction:
three different complete components, two of unequal orders, are
impossible in a non-cluster double-sized transitive EPPA host
with a nontrivial invariant block system. No co-P3 hypothesis
or arbitrary choice between Cases 1 and 2 remains. -/
theorem transitive_eppa_unequal_three_cliques
    {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hNonCluster : ¬ IsClusterGraph H)
    (hCluster : IsClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (x y z : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card)
    (hxz : x ≠ z) (hyz : y ≠ z)
    (hnxz : ¬ G.Adj x z) (hnyz : ¬ G.Adj y z) : False := by
  have hCoP3 : HasInducedCoP3 G :=
    cluster_unequal_degrees_has_induced_cop3
      G hCluster x y hDifferent
  exact transitive_eppa_unequal_three_cliques_impossible
    G H e heppa block hBlocks hSurj hTrans
    hNonCluster hCluster hCoP3 hManyBlocks hNontrivial
    hHostSize x y z hDifferent hxz hyz hnxz hnyz

end EPPAIII.BlockSystems
