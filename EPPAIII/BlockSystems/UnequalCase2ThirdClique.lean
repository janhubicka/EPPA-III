import EPPAIII.BlockSystems.UnequalCase2WithoutHomogeneity
import EPPAIII.DoubleCover.ClusterComponentEdges
import EPPAIII.DoubleCover.TaylorCountArithmetic

/-!
# Three distinct clique components imply the Taylor triangle budget

The earlier Case-2 theorem used the numerical inequality
  deg(x) + deg(y) + 2 < |G|
as an explicit hypothesis. Here it is derived from the existence
of a third distinct clique component. This also shows that two
different clique orders force distinct nonadjacent base vertices.

All counting is for the actual finite base graph; no clique-index
labelling, matching or additional EPPA action is assumed.
-/

namespace EPPAIII.BlockSystems

/-- Adjacent vertices of a disjoint union of cliques have the same
closed component and hence the same base degree. -/
theorem cluster_adjacent_equal_degrees {V : Type*}
    [Fintype V]
    (G : SimpleGraph V) (hCluster : IsClusterGraph G)
    (x y : V) (hxy : G.Adj x y) :
    (DoubleCover.clusterBaseNeighbours G x).card =
      (DoubleCover.clusterBaseNeighbours G y).card := by
  classical
  have hxInY : x ∈ DoubleCover.clusterBaseComponent G y :=
    (DoubleCover.mem_clusterBaseComponent_iff G y x).mpr
      (Or.inr hxy.symm)
  have hyInX : y ∈ DoubleCover.clusterBaseComponent G x :=
    (DoubleCover.mem_clusterBaseComponent_iff G x y).mpr
      (Or.inr hxy)
  have hComponents :
      DoubleCover.clusterBaseComponent G x =
        DoubleCover.clusterBaseComponent G y := by
    ext z
    constructor
    · intro hz
      rcases (DoubleCover.mem_clusterBaseComponent_iff G x z).mp hz with heq | hxz
      · subst z
        exact hxInY
      · exact DoubleCover.clusterBaseComponent_closed_under_edges
          G hCluster y x z hxInY hxz
    · intro hz
      rcases (DoubleCover.mem_clusterBaseComponent_iff G y z).mp hz with heq | hyz
      · subst z
        exact hyInX
      · exact DoubleCover.clusterBaseComponent_closed_under_edges
          G hCluster x y z hyInX hyz
  have hSizes := congrArg Finset.card hComponents
  rw [DoubleCover.clusterBaseComponent_card G x,
      DoubleCover.clusterBaseComponent_card G y] at hSizes
  omega

/-- Different clique degrees already mean that the two selected
base vertices are distinct and lie in different clique components. -/
theorem cluster_unequal_degrees_distinct_nonadjacent {V : Type*}
    [Fintype V]
    (G : SimpleGraph V) (hCluster : IsClusterGraph G)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    x ≠ y ∧ ¬ G.Adj x y := by
  constructor
  · intro h
    subst y
    exact hDifferent rfl
  · intro hxy
    exact hDifferent (cluster_adjacent_equal_degrees G hCluster x y hxy)

/-- Three pairwise different, mutually nonadjacent vertices in a
cluster graph represent three disjoint components; the first two
components and one point of the third fit into its vertex set. -/
theorem cluster_third_component_degree_budget {V : Type*}
    [Fintype V]
    (G : SimpleGraph V) (hCluster : IsClusterGraph G)
    (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnxy : ¬ G.Adj x y) (hnxz : ¬ G.Adj x z)
    (hnyz : ¬ G.Adj y z) :
    (DoubleCover.clusterBaseNeighbours G x).card +
      (DoubleCover.clusterBaseNeighbours G y).card + 2 <
        Fintype.card V := by
  classical
  let Cx := DoubleCover.clusterBaseComponent G x
  let Cy := DoubleCover.clusterBaseComponent G y
  have hDisj : Disjoint Cx Cy := by
    apply Finset.disjoint_left.mpr
    intro w hwx hwy
    have hxInY : x ∈ Cy := by
      rcases (DoubleCover.mem_clusterBaseComponent_iff G x w).mp hwx with heq | hxw
      · subst w
        exact hwy
      · exact DoubleCover.clusterBaseComponent_closed_under_edges
          G hCluster y w x hwy hxw.symm
    rcases (DoubleCover.mem_clusterBaseComponent_iff G y x).mp hxInY with heq | hyx
    · exact hxy heq
    · exact hnxy hyx.symm
  have hzNotX : z ∉ Cx := by
    intro hz
    rcases (DoubleCover.mem_clusterBaseComponent_iff G x z).mp hz with heq | hAdj
    · exact hxz heq.symm
    · exact hnxz hAdj
  have hzNotY : z ∉ Cy := by
    intro hz
    rcases (DoubleCover.mem_clusterBaseComponent_iff G y z).mp hz with heq | hAdj
    · exact hyz heq.symm
    · exact hnyz hAdj
  have hzNotUnion : z ∉ Cx ∪ Cy := by
    simpa only [Finset.mem_union, not_or] using
      (And.intro hzNotX hzNotY)
  have hCard :
      (insert z (Cx ∪ Cy)).card = Cx.card + Cy.card + 1 := by
    rw [Finset.card_insert_of_notMem hzNotUnion,
      Finset.card_union_of_disjoint hDisj]
  have hBound : (insert z (Cx ∪ Cy)).card ≤ Fintype.card V := by
    calc
      (insert z (Cx ∪ Cy)).card ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := Finset.card_univ
  have hxCard : Cx.card =
      (DoubleCover.clusterBaseNeighbours G x).card + 1 :=
    DoubleCover.clusterBaseComponent_card G x
  have hyCard : Cy.card =
      (DoubleCover.clusterBaseNeighbours G y).card + 1 :=
    DoubleCover.clusterBaseComponent_card G y
  omega

/-- Case-2 obstruction using a genuine third-component witness
rather than a separately assumed numerical triangle budget. -/
theorem transitive_eppa_case2_three_clique_representatives
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hCluster : IsClusterGraph G)
    (hCoP3 : HasInducedCoP3 G)
    (hCross : ∃ u v : V,
      G.Adj u v ∧ block (e u) ≠ block (e v))
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
  obtain ⟨hxy,hnxy⟩ :=
    cluster_unequal_degrees_distinct_nonadjacent
      G hCluster x y hDifferent
  have hThird :=
    cluster_third_component_degree_budget G hCluster
      x y z hxy hxz hyz hnxy hnxz hnyz
  exact transitive_eppa_case2_unequal_three_components
    G H e heppa block hBlocks hSurj hTrans
    hCluster hCoP3 hCross hManyBlocks hNontrivial
    hHostSize x y hDifferent hThird

end EPPAIII.BlockSystems
