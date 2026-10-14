import EPPAIII.BlockSystems.Case1NoUnoccupied
import EPPAIII.BlockSystems.UniformCrossBlockDegrees
import EPPAIII.BlockSystems.CrossBlockSizeEquation
import EPPAIII.BlockSystems.UnequalCase1Arithmetic

/-!
# Actual Case-1 two-block theorem in unequal-clique Lemma 3.12

This theorem combines the previously separated verified pieces:

* Case 1 EPPA and unequal selected block sizes imply all blocks
  induce cliques and every block meets the selected graph G.
* Genuine two-point EPPA and vertex transitivity yield a
  common cross-block neighbour degree r for all host vertices.
* The complete block quotient makes r positive.
* The no outside-outside cross-block edges property of Claim 3.14
  and the selected-edge internality make all inter-block edges
  mixed. The symmetric bipartite count now yields k_i+k_j=m
  for every distinct block pair.
* Unequal k_i therefore force exactly two host blocks.

No coherent EPPA action, pre-partitioned outside half, or
postulated cross-block degree matrix is used. The subsequent
r=1 perfect matching argument is not part of this theorem.
-/

namespace EPPAIII.BlockSystems

/-- Claim 3.15 up to the final perfect matching: the actual
double-sized transitive EPPA host has exactly two invariant
blocks under the unequal-clique Case-1 hypotheses. -/
theorem eppa_case1_exactly_two_host_blocks {V W B : Type*}
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
    Fintype.card B = 2 := by
  classical
  have hbc : b ≠ c := by
    intro h
    subst c
    exact hDifferent rfl
  have hOccupied : occupiedBlocks e block = Finset.univ :=
    eppa_case1_all_host_blocks_occupied
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hNotWhole hNonCluster m
      hUniformSize hDouble b c hb hc hDifferent
  have hOccupiedAll : ∀ j : B, j ∈ occupiedBlocks e block := by
    intro j
    rw [hOccupied]
    exact Finset.mem_univ _
  have hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y :=
    eppa_base_same_block_iff_eq_or_adj
      G H e heppa block hBlocks hOneEdge hNotWhole
  obtain ⟨r,hSelectedRegular⟩ :=
    eppa_selected_cross_block_degree_uniform
      G H e heppa block hBlocks hSurj hSame
      hOccupiedAll b c hb hc hbc
  have hCrossRegular : ∀ u : W, ∀ j : B, block u ≠ j →
      neighboursInBlock H block u j = r :=
    host_cross_block_degree_uniform
      H e block hBlocks hSurj hTrans
      hOccupiedAll r hSelectedRegular
  obtain ⟨_hAllBlocks,hQuotient,_hAtMostOne⟩ :=
    eppa_case1_quotient_and_unoccupied_bound
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hNotWhole hNonCluster m
      hUniformSize hDouble b c hb hc hDifferent
  have hr : 0 < r :=
    positive_common_cross_block_degree
      H block r hCrossRegular hQuotient b c hbc
  have hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y) :=
    eppa_base_edges_internal_of_one
      G H e heppa block hBlocks hOneEdge
  have hOutsideInside : ∀ u v : W,
      u ∉ Set.range e → v ∉ Set.range e →
      H.Adj u v → block u = block v := by
    intro u v hu hv huv
    exact no_outside_cross_block_edges G H e heppa.1
      block hBlocks hTrans hSelectedInside hDouble
      u v hu hv huv
  have hPair : ∀ i j : B, i ≠ j →
      (selectedInBlock e block i).card +
        (selectedInBlock e block j).card = m := by
    intro i j hij
    exact selected_occupied_pairwise_complementary
      G H e heppa.1 block hSelectedInside hOutsideInside
      m hUniformSize r hr hCrossRegular i j hij
  exact all_occupied_complementary_unequal_two_blocks
    (fun i : B => (selectedInBlock e block i).card) m
    hPair ⟨b,c,hDifferent⟩

end EPPAIII.BlockSystems
