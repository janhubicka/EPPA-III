import EPPAIII.BlockSystems.UnequalCase1DegreeOne
import EPPAIII.BlockSystems.UnitCrossMatching

/-!
# Complete unequal-clique Case-1 perfect-matching conclusion

The earlier proof derived from genuine EPPA and vertex transitivity
that the host has exactly two occupied invariant clique blocks and
that each host vertex has one neighbour in the other block.

The unit-degree result turns the actual cross-block graph into
a perfect matching: each host vertex has exactly one cross-block
neighbour. This completes the corrected Case-1 classification
used in unequal-clique Lemma 3.12.

The proof makes no assumption about an already-labelled outside
half or a coherent lifting of partial automorphisms. It does not
claim to cover the separate Case-2 Taylor-double reduction.
-/

namespace EPPAIII.BlockSystems

/-- The actual double-sized non-cluster transitive EPPA host in
unequal-clique Case 1 consists of exactly two invariant blocks
with cross-block edges forming a perfect matching. -/
theorem eppa_case1_exactly_two_blocks_with_matching {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hOneEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hNotWhole : ∃ x y : V, block (e x) ≠ block (e y))
    (hNonCluster : ¬ IsClusterGraph H)
    (m : ℕ)
    (hUniformSize : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (b c : B)
    (hb : b ∈ occupiedBlocks e block)
    (hc : c ∈ occupiedBlocks e block)
    (hDifferent :
      (selectedInBlock e block b).card ≠
        (selectedInBlock e block c).card) :
    Fintype.card B = 2 ∧
      ∀ u : W, ∃! v : W, (crossBlockGraph H block).Adj u v := by
  classical
  have hbc : b ≠ c := by
    intro h
    subst c
    exact hDifferent rfl
  have hCard : Fintype.card B = 2 :=
    eppa_case1_exactly_two_host_blocks
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hNotWhole hNonCluster m hUniformSize
      hDouble b c hb hc hDifferent
  have hTwo : ∀ x : B, x = b ∨ x = c :=
    labels_exhaust_card_two b c hbc hCard
  obtain ⟨r,hrOne,hDegree⟩ :=
    eppa_case1_cross_degree_eq_one
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hNotWhole hNonCluster m hUniformSize
      hDouble b c hb hc hDifferent
  have hUnit : ∀ u : W, ∀ j : B, block u ≠ j →
      neighboursInBlock H block u j = 1 := by
    intro u j hj
    simpa only [hrOne] using hDegree u j hj
  exact ⟨hCard,
    two_block_cross_graph_perfect_matching H block
      b c hbc hTwo hUnit⟩

end EPPAIII.BlockSystems
