import EPPAIII.BlockSystems.UnequalMatchingTaylor

/-!
# Final structural classification for unequal clique orders

The selected base is a union of complete graphs with two different
clique sizes. The host is vertex-transitive, non-cluster,
imprimitive and has twice as many vertices.

The proof uses only genuine EPPA, the actual invariant block map and
the already verified counting lemmas. Regardless of whether a
selected edge is internal to a block or crosses blocks, the
host is a Taylor double, with uniformly optional mate matching.

The independent no-third-component theorem also says that any two
unequal selected clique representatives exhaust G. The manuscript's
assumption "non-homogeneous host" has not been substituted silently:
the elementary implication from a transitive cluster host to a
homogeneous host is kept as a separate bridge.
-/

namespace EPPAIII.BlockSystems

/-- Complete Taylor-pair structural conclusion from unequal base
clique degrees in a real invariant imprimitive EPPA host. -/
theorem transitive_eppa_unequal_clique_actual_host_is_taylor
    {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hNonCluster : ¬ IsClusterGraph H)
    (hCluster : IsClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    ∃ φ : Bool × V ≃ W,
      (∀ v : V, φ (false,v) = e v) ∧
      ∃ mate : Bool,
        (∀ v : V, H.Adj (φ (false,v)) (φ (true,v)) ↔
          mate = true) ∧
        DoubleCover.RepresentsPairPattern G
          (pullbackGraph H φ) DoubleCover.taylor := by
  classical
  have hNonHom : ¬ DoubleCover.IsHomogeneousGraph G :=
    nonhomogeneous_of_unequal_base_degrees G x y hDifferent
  have hCoP3 : HasInducedCoP3 G :=
    cluster_unequal_degrees_has_induced_cop3
      G hCluster x y hDifferent
  obtain ⟨b₀,hb₀⟩ := hNontrivial
  let m : ℕ :=
    ((Finset.univ : Finset W).filter
      (fun w => block w = b₀)).card
  have hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m := by
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
      G H e heppa block hBlocks hNonHom hBound
  have hPositive :
      0 < (DoubleCover.clusterBaseNeighbours G x).card ∨
      0 < (DoubleCover.clusterBaseNeighbours G y).card := by
    omega
  have hSomeEdge : ∃ a b : V, G.Adj a b := by
    rcases hPositive with hx | hy
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp hx
      exact ⟨x,v,by
        simpa [DoubleCover.clusterBaseNeighbours] using hv⟩
    · obtain ⟨v,hv⟩ := Finset.card_pos.mp hy
      exact ⟨y,v,by
        simpa [DoubleCover.clusterBaseNeighbours] using hv⟩
  obtain ⟨a,b,hab⟩ := hSomeEdge
  by_cases hInside : block (e a) = block (e b)
  · have hMatching :
        ∀ u : W, ∃! v : W,
          (crossBlockGraph H block).Adj u v :=
      (eppa_case1_unequal_base_degrees_force_matching
        G H e heppa block hBlocks hSurj hTrans
        ⟨a,b,hab,hInside⟩ hNotWhole hNonCluster m
        hUniform hHostSize x y hDifferent).2
    exact eppa_case1_perfect_matching_is_taylor_up_to_mate
      G H e heppa block hBlocks
      ⟨a,b,hab,hInside⟩ hNotWhole
      hNonHom hHostSize hMatching
  · exact transitive_eppa_crossing_edge_taylor_up_to_mate
      G H e heppa block hBlocks hSurj hTrans
      hNonHom hCoP3 ⟨a,b,hab,hInside⟩ hManyBlocks
      ⟨b₀,hb₀⟩ hHostSize

/-- Complete elementary core of the unequal-clique classification:
no third selected component, and the actual host has Taylor
inter-fibre adjacency, with uniformly optional mate edges. -/
theorem transitive_eppa_unequal_two_cliques_and_taylor
    {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hNonCluster : ¬ IsClusterGraph H)
    (hCluster : IsClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    (∀ z : V, (z = x ∨ G.Adj x z) ∨
      (z = y ∨ G.Adj y z)) ∧
    (∃ φ : Bool × V ≃ W,
      (∀ v : V, φ (false,v) = e v) ∧
      ∃ mate : Bool,
        (∀ v : V, H.Adj (φ (false,v)) (φ (true,v)) ↔
          mate = true) ∧
        DoubleCover.RepresentsPairPattern G
          (pullbackGraph H φ) DoubleCover.taylor) := by
  constructor
  · intro z
    exact transitive_eppa_unequal_two_base_components
      G H e heppa block hBlocks hSurj hTrans
      hNonCluster hCluster hManyBlocks hNontrivial
      hHostSize x y hDifferent z
  · exact transitive_eppa_unequal_clique_actual_host_is_taylor
      G H e heppa block hBlocks hSurj hTrans
      hNonCluster hCluster hManyBlocks hNontrivial
      hHostSize x y hDifferent

end EPPAIII.BlockSystems
