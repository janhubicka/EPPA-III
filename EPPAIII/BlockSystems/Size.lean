import EPPAIII.BlockSystems.FilledBlock
import EPPAIII.DoubleCover.CompleteTaylor

/-!
# The finite block-size reduction in Claim 3.4

Assume the initial nontrivial block partition is invariant and uniform,
as happens for a transitive graph. The equal-fibre cardinal formula is
stated explicitly: #blocks * sizeOfEachBlock = #verticesOfHost.

We prove the two counting consequences used in the manuscript:
1. If all of G lies in one block, it fills that block, hence G is
   homogeneous by FilledBlock.
2. Otherwise, induced P3 and co-P3 show G meets every block at most
   once; the double-size equation forces exactly n blocks of size 2.

The derivation of the equal-size cardinal formula from actual host
vertex-transitivity is a separate formalization step.
-/

namespace EPPAIII.BlockSystems

/-- If an injective copy of the n-vertex graph lies within a block of
size at most n, it occupies the entire block. -/
theorem fills_block_of_card_bound {V W B : Type*}
    [Fintype V] [Fintype W]
    (e : V ↪ W) (block : W → B) (b₀ : B)
    (hInside : ∀ x : V, block (e x) = b₀)
    (hBound :
      ((Finset.univ : Finset W).filter (fun w => block w = b₀)).card
        ≤ Fintype.card V) :
    ∀ w : W, block w = b₀ → ∃ x : V, e x = w := by
  classical
  let image : Finset W := (Finset.univ : Finset V).image e
  let fibre : Finset W :=
    (Finset.univ : Finset W).filter (fun w => block w = b₀)
  have hSubset : image ⊆ fibre := by
    intro w hw
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
    have hbw : block w = b₀ := by
      rw [← hx]
      exact hInside x
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbw⟩
  have hImageCard : image.card = Fintype.card V := by
    simpa [image] using
      (Finset.card_image_of_injective
        (Finset.univ : Finset V) e.injective)
  have hCardLe : fibre.card ≤ image.card := by
    rw [hImageCard]
    exact hBound
  have hEq : image = fibre :=
    Finset.eq_of_subset_of_card_le hSubset hCardLe
  intro w hw
  have hMem : w ∈ fibre :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
  have hImage : w ∈ image := by
    rw [hEq]
    exact hMem
  obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hImage
  exact ⟨x,hx⟩

/-- In a transitive, uniformly partitioned double-sized host with at
least two blocks, the size of each block is at most |G|. -/
theorem regular_block_size_le_half
    (numberOfBlocks blockSize n : ℕ)
    (hManyBlocks : 2 ≤ numberOfBlocks)
    (hOrder : numberOfBlocks * blockSize = 2 * n) :
    blockSize ≤ n := by
  have hh : 2 * blockSize ≤ numberOfBlocks * blockSize :=
    Nat.mul_le_mul_right blockSize hManyBlocks
  omega

/-- Non-homogeneity excludes the case in which all selected vertices
are in a single block. The proof uses no group-action homogeneity
classification, only the actual EPPA embedding. -/
theorem nonhomogeneous_not_whole_block {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hBlockBound : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card
        ≤ Fintype.card V) :
    ∃ x y : V, block (e x) ≠ block (e y) := by
  classical
  obtain ⟨xe,ye,_,_,_,_,_⟩ :=
    DoubleCover.edge_and_nonedge_of_nonhomogeneous G hNonHomogeneous
  by_contra hNo
  have hAll (x y : V) : block (e x) = block (e y) := by
    by_contra hne
    exact hNo ⟨x,y,hne⟩
  let b₀ : B := block (e xe)
  have hInside : ∀ x : V, block (e x) = b₀ := fun x => hAll x xe
  have hFilled : ∀ w : W, block w = b₀ → ∃ x : V, e x = w :=
    fills_block_of_card_bound e block b₀ hInside (hBlockBound b₀)
  exact hNonHomogeneous
    (homogeneous_of_filled_invariant_block
      G H e heppa block hBlocks b₀ hInside hFilled)

/-- Main counted-transversal result, conditional only on the
invariant uniform block partition and the double-size equation.
In a transitive graph those conditions follow from the action
on the block partition. -/
theorem invariant_blocks_are_pairs {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [Fintype B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hNonCluster : ¬ IsClusterGraph G)
    (hNonCoCluster : ¬ IsCoClusterGraph G)
    (blockSize : ℕ)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hBlockSize : 2 ≤ blockSize)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card =
        blockSize)
    (hOrder : Fintype.card B * blockSize = 2 * Fintype.card V) :
    Function.Injective (fun x : V => block (e x)) ∧
      Fintype.card B = Fintype.card V ∧ blockSize = 2 := by
  classical
  have hBound : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card
        ≤ Fintype.card V := by
    intro b
    rw [hUniform b]
    exact regular_block_size_le_half
      (Fintype.card B) blockSize (Fintype.card V)
      hManyBlocks hOrder
  have hNotWhole := nonhomogeneous_not_whole_block
    G H e heppa block hBlocks hNonHomogeneous hBound
  have hTransversal := transversal_of_noncluster
    G H e heppa block hBlocks
    hNonCluster hNonCoCluster hNotWhole
  have hNumber : Fintype.card V ≤ Fintype.card B :=
    Fintype.card_le_of_injective
      (fun x : V => block (e x)) hTransversal
  obtain ⟨hB,hM⟩ := transversal_double_count
    (Fintype.card B) blockSize (Fintype.card V)
    (by omega) hBlockSize hNumber hOrder
  exact ⟨hTransversal,hB,hM⟩

end EPPAIII.BlockSystems
