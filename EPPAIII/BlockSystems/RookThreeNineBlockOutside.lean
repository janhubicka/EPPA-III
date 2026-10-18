import EPPAIII.BlockSystems.FilledInvariantHalf
import EPPAIII.BlockSystems.RookThreeActualBlocks
import EPPAIII.BlockSystems.Size

/-!
# The size-nine case of the R3 complementary-half lemma

If every invariant imprimitivity block of an 18-vertex
vertex-transitive EPPA host has nine vertices, there are
exactly two blocks. The primitive rook action and EPPA imply
all nine selected vertices fill one block. An actual host
automorphism therefore identifies the other block, with
its induced graph, with the selected rook graph.

Cross-block edges need not vanish. No abstract outside action
or classification of homogeneous graphs is used.
-/

namespace EPPAIII.BlockSystems

/-- Every 9+9 imprimitive R3 EPPA witness has the
other half isomorphic to R3, fixing the selected copy. -/
theorem rook_eppa_nine_block_outside_is_rook
    {W B : Type*}
    [Fintype W] [Fintype B] [DecidableEq B]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hTrans : IsVertexTransitive H)
    (h18 : Fintype.card W = 18)
    (hNine : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = 9) :
    ∃ f : rookVertex ≃ {w : W // w ∈ finiteOutside e},
      H.comap (fun x => (f x).val) = rookThreeGraph := by
  classical
  have hNumber : Fintype.card B * 9 = 18 := by
    have h := uniform_partition_card_formula block 9 hNine
    exact h.trans h18
  have hBlocksTwo : Fintype.card B = 2 := by omega
  rcases rook_eppa_selected_block_transversal_or_single
      H e heppa block hBlocks with hInj | hAll
  · have hNineBlocks : 9 ≤ Fintype.card B := by
      have h := Fintype.card_le_of_injective
        (fun x : rookVertex => block (e x)) hInj
      simpa [rookVertex] using h
    omega
  · let b₀ : B := block (e (0,0))
    have hSelected (x : rookVertex) :
        block (e x) = b₀ := hAll x (0,0)
    have hFilled :
        ∀ w : W, block w = b₀ → ∃ x : rookVertex, e x = w :=
      fills_block_of_card_bound e block b₀ hSelected (by
        rw [hNine b₀]
        simp [rookVertex])
    have hDouble :
        Fintype.card W = 2 * Fintype.card rookVertex := by
      simpa [rookVertex] using h18
    exact transitive_outside_equiv_of_filled_invariant_half
      rookThreeGraph H e heppa.1 block hBlocks b₀
      hSelected hFilled hDouble hTrans

end EPPAIII.BlockSystems
