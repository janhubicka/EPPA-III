import EPPAIII.BlockSystems.RookThreePrimitivePartition

/-!
# The exact 2-or-9 invariant block sizes in the R3 exception

The 3×3 rook selected base is primitive under genuine EPPA:
either all nine selected vertices lie in one host block or
they meet nine different blocks. Host vertex transitivity
makes all nonempty invariant block fibres equally large.
Since |H|=18 and all blocks have size at least two, their
common size is respectively 9 or 2.

This proves current Claim 6.15, with no Gardiner classification,
no chosen action on outside vertices, and no coherent EPPA lifts.
-/

namespace EPPAIII.BlockSystems

/-- In an eighteen-vertex vertex-transitive EPPA host of R3,
every nontrivial imprimitivity block has size 2 or 9. -/
theorem rook_eppa_nontrivial_imprimitive_block_sizes
    {W B : Type*}
    [Fintype W] [Fintype B] [DecidableEq B]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (h18 : Fintype.card W = 18)
    (hMany : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card) :
    (∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = 2) ∨
    (∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = 9) := by
  classical
  obtain ⟨b₀,hLarge⟩ := hNontrivial
  let m : ℕ :=
    ((Finset.univ : Finset W).filter
      (fun w => block w = b₀)).card
  have hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m := by
    intro b
    exact transitive_block_fibres_equal
      H block hTrans hBlocks hSurj b b₀
  have hmLower : 2 ≤ m := hLarge
  have hCount : Fintype.card B * m = 18 :=
    (uniform_partition_card_formula block m hUniform).trans h18
  rcases rook_eppa_selected_block_transversal_or_single
      H e heppa block hBlocks with hInject | hAll
  · left
    have hNumber : 9 ≤ Fintype.card B := by
      have h := Fintype.card_le_of_injective
        (fun x : rookVertex => block (e x)) hInject
      simpa [rookVertex] using h
    have hProduct : 9 * m ≤ Fintype.card B * m :=
      Nat.mul_le_mul_right m hNumber
    have hm : m = 2 := by omega
    intro b
    rw [hUniform b]
    exact hm
  · right
    let bSel : B := block (e (0,0))
    let S : Finset W :=
      (Finset.univ : Finset rookVertex).image e
    let F : Finset W :=
      (Finset.univ : Finset W).filter
        (fun w => block w = bSel)
    have hInBlock (x : rookVertex) : block (e x) = bSel :=
      hAll x (0,0)
    have hSubset : S ⊆ F := by
      intro w hw
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hInBlock x⟩
    have hSelectedCard : S.card = 9 := by
      have h := Finset.card_image_of_injective
        (Finset.univ : Finset rookVertex) e.injective
      simpa [S,rookVertex] using h
    have hBlockCard : F.card = m := hUniform bSel
    have hmAtLeastNine : 9 ≤ m := by
      have h := Finset.card_le_card hSubset
      omega
    have hDoubleBound : 2 * m ≤ Fintype.card B * m :=
      Nat.mul_le_mul_right m hMany
    have hm : m = 9 := by omega
    intro b
    rw [hUniform b]
    exact hm

end EPPAIII.BlockSystems
