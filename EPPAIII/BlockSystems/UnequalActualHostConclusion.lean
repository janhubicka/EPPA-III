import EPPAIII.BlockSystems.UnequalCaseCoP3
import EPPAIII.BlockSystems.UnequalCase2Taylor

/-!
# Unequal clique sizes: actual-host structural dichotomy

This is the direct proof boundary of current Lemma 6.6 (formerly
Lemma 3.12). It combines the genuinely imprimitive, vertex-transitive
EPPA arguments instead of postulating an indexed complementary half.

The host non-cluster hypothesis is explicit. Removing it from the
manuscript's "non-homogeneous host" assumption requires the elementary
classification of transitive cluster graphs as homogeneous, which
is a distinct interface lemma.

No claim is made yet that the two-block perfect matching has been
identified by a labelled graph equivalence with the paper's named
double; that is the final realization step.
-/

namespace EPPAIII.BlockSystems

/-- Under unequal selected clique degrees, the actual non-cluster
host is either:
(1) partitioned into exactly two invariant host blocks, with a
    perfect matching of cross-block edges, or
(2) the Taylor pair-pattern double of the base, with a uniform
    optional matching between fibre mates.
All block-size, block-occupancy and non-homogeneity facts needed by
the earlier case theorems are derived here, not assumed. -/
theorem transitive_eppa_unequal_clique_actual_host_dichotomy
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
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    (Fintype.card B = 2 ∧
      ∀ u : W, ∃! v : W, (crossBlockGraph H block).Adj u v) ∨
    (∃ φ : Bool × V ≃ W,
      (∀ v : V, φ (false,v) = e v) ∧
      ∃ mate : Bool,
        (∀ v : V, H.Adj (φ (false,v)) (φ (true,v)) ↔
          mate = true) ∧
        DoubleCover.RepresentsPairPattern
          G (pullbackGraph H φ) DoubleCover.taylor) := by
  classical
  have hNonHom : ¬ DoubleCover.IsHomogeneousGraph G :=
    nonhomogeneous_of_unequal_base_degrees G x y hDifferent
  have hCoP3 : HasInducedCoP3 G :=
    cluster_unequal_degrees_has_induced_cop3
      G hCluster x y hDifferent
  obtain ⟨b₀,hb₀⟩ := hNontrivial
  let m : ℕ :=
    ((Finset.univ : Finset W).filter (fun w => block w = b₀)).card
  have hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m := by
    intro b
    exact transitive_block_fibres_equal
      H block hTrans hBlocks hSurj b b₀
  have hCount : Fintype.card B * m = 2 * Fintype.card V :=
    (uniform_partition_card_formula block m hUniform).trans hHostSize
  have hBound : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card ≤ Fintype.card V := by
    intro b
    rw [hUniform b]
    exact regular_block_size_le_half
      (Fintype.card B) m (Fintype.card V) hManyBlocks hCount
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
  · left
    exact eppa_case1_unequal_base_degrees_force_matching
      G H e heppa block hBlocks hSurj hTrans
      ⟨a,b,hab,hInside⟩ hNotWhole hNonCluster m
      hUniform hHostSize x y hDifferent
  · right
    exact transitive_eppa_crossing_edge_taylor_up_to_mate
      G H e heppa block hBlocks hSurj hTrans
      hNonHom hCoP3 ⟨a,b,hab,hInside⟩ hManyBlocks
      ⟨b₀,hb₀⟩ hHostSize

/-- No third clique component is possible: every base vertex lies
in the complete component of one of two fixed vertices of unequal
degree. Unlike the manuscript's cardinality argument, no quotient
count or guessed permutation of outside blocks is postulated. -/
theorem transitive_eppa_unequal_two_base_components
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
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card)
    (z : V) :
    (z = x ∨ G.Adj x z) ∨ (z = y ∨ G.Adj y z) := by
  classical
  by_cases hx : z = x ∨ G.Adj x z
  · exact Or.inl hx
  · by_cases hy : z = y ∨ G.Adj y z
    · exact Or.inr hy
    · have hxz : x ≠ z := by
        intro h
        exact hx (Or.inl h.symm)
      have hyz : y ≠ z := by
        intro h
        exact hy (Or.inl h.symm)
      have hnxz : ¬ G.Adj x z := by
        intro h
        exact hx (Or.inr h)
      have hnyz : ¬ G.Adj y z := by
        intro h
        exact hy (Or.inr h)
      exact False.elim
        (transitive_eppa_unequal_three_cliques
          G H e heppa block hBlocks hSurj hTrans
          hNonCluster hCluster hManyBlocks hNontrivial
          hHostSize x y z hDifferent hxz hyz hnxz hnyz)

end EPPAIII.BlockSystems
