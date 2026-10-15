import EPPAIII.BlockSystems.UnequalCase1FromDegrees
import EPPAIII.BlockSystems.UnequalCase2ThirdClique

/-!
# No three unequal clique components in a non-cluster imprimitive host

The repaired Case-1 theorem identifies the selected fibre sizes with
base clique orders and forces two blocks joined by a perfect matching.
The repaired Case-2 theorem excludes the Taylor double when a third
clique component exists. Here we perform the actual dichotomy on
the status of one selected edge relative to the invariant partition.

All uniform block sizes, the existence of an internal/external base
edge, and non-concentration of the selected copy are derived from
the double-sized vertex-transitive EPPA host and unequal base degrees.
The remaining assumptions are an invariant nontrivial block system,
non-cluster H, cluster G and a third clique representative.
-/

namespace EPPAIII.BlockSystems

/-- In Case 1, distinct nonadjacent selected base vertices must
lie in different blocks of the actual invariant host partition. -/
theorem eppa_case1_nonadjacent_selected_blocks_differ {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hOneEdge : ∃ a b : V,
      G.Adj a b ∧ block (e a) = block (e b))
    (hNotWhole : ∃ a b : V, block (e a) ≠ block (e b))
    (u v : V) (huv : u ≠ v) (hNonedge : ¬ G.Adj u v) :
    block (e u) ≠ block (e v) := by
  intro hSame
  rcases (eppa_base_same_block_iff_eq_or_adj
      G H e heppa block hBlocks hOneEdge hNotWhole u v).mp
      hSame with heq | hAdj
  · exact huv heq
  · exact hNonedge hAdj

/-- The full unequal-clique third-component obstruction for an actual
invariant double-sized non-cluster EPPA host. Neither a Case-1/Case-2
choice nor auxiliary block occupancy and triangle-size inequalities
are hypotheses: all are deduced in the proof. -/
theorem transitive_eppa_unequal_three_cliques_impossible
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
    (hCoP3 : HasInducedCoP3 G)
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
  classical
  have hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G :=
    nonhomogeneous_of_unequal_base_degrees G x y hDifferent
  obtain ⟨b₀,hb₀⟩ := hNontrivial
  let m : ℕ :=
    ((Finset.univ : Finset W).filter (fun w => block w = b₀)).card
  have hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card = m := by
    intro b
    exact transitive_block_fibres_equal
      H block hTrans hBlocks hSurj b b₀
  have hOrder : Fintype.card B * m = 2 * Fintype.card V :=
    (uniform_partition_card_formula block m hUniform).trans hHostSize
  have hBound : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card ≤ Fintype.card V := by
    intro b
    rw [hUniform b]
    exact regular_block_size_le_half
      (Fintype.card B) m (Fintype.card V) hManyBlocks hOrder
  have hNotWhole : ∃ a b : V, block (e a) ≠ block (e b) :=
    nonhomogeneous_not_whole_block
      G H e heppa block hBlocks hNonHomogeneous hBound
  have hPositive :
      0 < (DoubleCover.clusterBaseNeighbours G x).card ∨
      0 < (DoubleCover.clusterBaseNeighbours G y).card := by
    omega
  have hSomeEdge : ∃ a b : V, G.Adj a b := by
    rcases hPositive with hx | hy
    · obtain ⟨v,hv⟩ :=
        Finset.card_pos.mp hx
      exact ⟨x,v,by simpa [DoubleCover.clusterBaseNeighbours] using hv⟩
    · obtain ⟨v,hv⟩ :=
        Finset.card_pos.mp hy
      exact ⟨y,v,by simpa [DoubleCover.clusterBaseNeighbours] using hv⟩
  obtain ⟨a,b,hab⟩ := hSomeEdge
  by_cases hInside : block (e a) = block (e b)
  · let hOneEdge : ∃ u v : V,
        G.Adj u v ∧ block (e u) = block (e v) :=
      ⟨a,b,hab,hInside⟩
    have hMatch :
        Fintype.card B = 2 ∧
        ∀ u : W, ∃! v : W, (crossBlockGraph H block).Adj u v :=
      eppa_case1_unequal_base_degrees_force_matching
        G H e heppa block hBlocks hSurj hTrans
        hOneEdge hNotWhole hNonCluster m hUniform
        hHostSize x y hDifferent
    obtain ⟨hxy,hnxy⟩ :=
      cluster_unequal_degrees_distinct_nonadjacent
        G hCluster x y hDifferent
    have hXY :
        block (e x) ≠ block (e y) :=
      eppa_case1_nonadjacent_selected_blocks_differ
        G H e heppa block hBlocks
        hOneEdge hNotWhole x y hxy hnxy
    have hXZ :
        block (e x) ≠ block (e z) :=
      eppa_case1_nonadjacent_selected_blocks_differ
        G H e heppa block hBlocks
        hOneEdge hNotWhole x z hxz hnxz
    have hYZ :
        block (e y) ≠ block (e z) :=
      eppa_case1_nonadjacent_selected_blocks_differ
        G H e heppa block hBlocks
        hOneEdge hNotWhole y z hyz hnyz
    have hAll : ∀ c : B,
        c = block (e x) ∨ c = block (e y) :=
      labels_exhaust_card_two
        (block (e x)) (block (e y)) hXY hMatch.1
    rcases hAll (block (e z)) with hZX | hZY
    · exact hXZ hZX.symm
    · exact hYZ hZY.symm
  · exact transitive_eppa_case2_three_clique_representatives
      G H e heppa block hBlocks hSurj hTrans
      hCluster hCoP3 ⟨a,b,hab,hInside⟩ hManyBlocks
      ⟨b₀,hb₀⟩ hHostSize x y z hDifferent
      hxz hyz hnxz hnyz

end EPPAIII.BlockSystems
