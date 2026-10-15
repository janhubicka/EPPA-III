import EPPAIII.BlockSystems.UnequalCase1Matching
import EPPAIII.DoubleCover.TaylorCountArithmetic

/-!
# The selected clique in a Case-1 block is the closed base component

The previous Case-1 proof assumed unequal *selected block occupancy*
counts. This file identifies them exactly with base clique sizes,
using the genuine EPPA-induced block relation. No outside partition,
coherent EPPA lifts or arbitrary clique decomposition is assumed.
-/

namespace EPPAIII.BlockSystems

/-- Under Case-1 block separation, the selected vertices of the
block containing x are precisely x and its base neighbours. -/
theorem eppa_case1_selected_block_eq_component {V W B : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hOneEdge : ∃ u v : V,
      G.Adj u v ∧ block (e u) = block (e v))
    (hNotWhole : ∃ u v : V, block (e u) ≠ block (e v))
    (x : V) :
    selectedInBlock e block (block (e x)) =
      DoubleCover.clusterBaseComponent G x := by
  classical
  ext y
  calc
    y ∈ selectedInBlock e block (block (e x)) ↔
        block (e y) = block (e x) := by
          simp [selectedInBlock]
    _ ↔ y = x ∨ G.Adj y x :=
      eppa_base_same_block_iff_eq_or_adj
        G H e heppa block hBlocks hOneEdge hNotWhole y x
    _ ↔ y ∈ DoubleCover.clusterBaseComponent G x :=
      (or_congr Iff.rfl (G.adj_comm y x)).trans
        (DoubleCover.mem_clusterBaseComponent_iff G x y).symm

/-- Consequently the selected occupancy equals the base degree
plus one, even if other host vertices occupy the same block. -/
theorem eppa_case1_selected_block_card_eq_degree_add_one {V W B : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hOneEdge : ∃ u v : V,
      G.Adj u v ∧ block (e u) = block (e v))
    (hNotWhole : ∃ u v : V, block (e u) ≠ block (e v))
    (x : V) :
    (selectedInBlock e block (block (e x))).card =
      (DoubleCover.clusterBaseNeighbours G x).card + 1 := by
  rw [eppa_case1_selected_block_eq_component
    G H e heppa block hBlocks hOneEdge hNotWhole x]
  exact DoubleCover.clusterBaseComponent_card G x

/-- Actual Case-1 matching conclusion, replacing unequal selected
block counts by the intrinsic inequality of two base vertex degrees. -/
theorem eppa_case1_unequal_base_degrees_force_matching {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hOneEdge : ∃ u v : V,
      G.Adj u v ∧ block (e u) = block (e v))
    (hNotWhole : ∃ u v : V, block (e u) ≠ block (e v))
    (hNonCluster : ¬ IsClusterGraph H)
    (m : ℕ)
    (hUniformSize : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    Fintype.card B = 2 ∧
      ∀ u : W, ∃! v : W, (crossBlockGraph H block).Adj u v := by
  have hx := eppa_case1_selected_block_card_eq_degree_add_one
    G H e heppa block hBlocks hOneEdge hNotWhole x
  have hy := eppa_case1_selected_block_card_eq_degree_add_one
    G H e heppa block hBlocks hOneEdge hNotWhole y
  have hDifferentBlocks :
      (selectedInBlock e block (block (e x))).card ≠
        (selectedInBlock e block (block (e y))).card := by
    intro heq
    exact hDifferent (by omega)
  have hxOccupied :
      block (e x) ∈ occupiedBlocks e block :=
    (mem_occupiedBlocks e block (block (e x))).mpr ⟨x,rfl⟩
  have hyOccupied :
      block (e y) ∈ occupiedBlocks e block :=
    (mem_occupiedBlocks e block (block (e y))).mpr ⟨y,rfl⟩
  exact eppa_case1_exactly_two_blocks_with_matching
    G H e heppa block hBlocks hSurj hTrans
    hOneEdge hNotWhole hNonCluster m hUniformSize
    hDouble (block (e x)) (block (e y))
    hxOccupied hyOccupied hDifferentBlocks

end EPPAIII.BlockSystems
