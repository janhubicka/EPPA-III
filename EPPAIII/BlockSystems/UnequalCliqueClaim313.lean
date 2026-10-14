import EPPAIII.BlockSystems.SelectedBlockArithmetic
import EPPAIII.BlockSystems.BlockStabilizerMajority
import EPPAIII.BlockSystems.UnequalCliqueBaseBlocks

/-!
# Complete Case-1 clique-block deduction (Claim 3.13)

Under actual EPPA and an invariant, uniformly sized block system,
assume that some selected edge is internal, not all selected vertices
lie in one block, and two blocks contain different numbers of
selected vertices. The two-point EPPA separation theorem says that
the selected vertices in each block form a clique of the base graph.

Double-size counting makes one of these cliques occupy strictly
more than half its host block. The setwise block stabiliser is
transitive and the induced block graph regular; hence that block
is complete, and host vertex transitivity transfers completeness
to all invariant blocks.

No ordering of the clique components or coherent lifts are needed.
This is the complete graph-theoretic bridge for Claim 3.13 under
the explicit Case-1 hypotheses. The later Claim 3.14 and matching
classification remain independent proof obligations.
-/

namespace EPPAIII.BlockSystems

/-- The selected vertices inside block b, retyped as vertices
of its induced graph. -/
noncomputable def selectedBlockPoints {V W B : Type*}
    [Fintype V] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (b : B) :
    Finset (BlockFiber block b) := by
  classical
  exact (selectedInBlock e block b).attach.image
    (fun (x : {z : V // z ∈ selectedInBlock e block b}) =>
      (⟨e x.1,
        (Finset.mem_filter.mp
          (show x.1 ∈ selectedInBlock e block b from x.2)).2⟩ :
        BlockFiber block b))

/-- Retyping along an injective embedding preserves the size
of the selected part of a block. -/
theorem selectedBlockPoints_card {V W B : Type*}
    [Fintype V] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (b : B) :
    (selectedBlockPoints e block b).card =
      (selectedInBlock e block b).card := by
  classical
  let f : {x : V // x ∈ selectedInBlock e block b} →
      BlockFiber block b := fun x =>
        ⟨e x.1, (Finset.mem_filter.mp
          (show x.1 ∈ selectedInBlock e block b from x.2)).2⟩
  have hInject : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hxy
  have hCard :=
    Finset.card_image_of_injective
      ((selectedInBlock e block b).attach) hInject
  simpa [selectedBlockPoints, f] using hCard

/-- The selected subset of a block is a clique when equality of
selected block labels is the same as adjacency-or-equality in G. -/
theorem selectedBlockPoints_clique {V W B : Type*}
    [Fintype V] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (he : IsInducedGraphEmbedding G H e)
    (block : W → B) (b : B)
    (hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y) :
    (inducedBlockGraph H block b).IsClique
      (selectedBlockPoints e block b : Set (BlockFiber block b)) := by
  classical
  intro u hu v hv huv
  change H.Adj u.1 v.1
  unfold selectedBlockPoints at hu hv
  obtain ⟨x,_,hxu⟩ := Finset.mem_image.mp hu
  obtain ⟨y,_,hyv⟩ := Finset.mem_image.mp hv
  have hxBlock : block (e x.1) = b :=
    (Finset.mem_filter.mp x.2).2
  have hyBlock : block (e y.1) = b :=
    (Finset.mem_filter.mp y.2).2
  have hSameBlock : block (e x.1) = block (e y.1) :=
    hxBlock.trans hyBlock.symm
  rcases (hSame x.1 y.1).mp hSameBlock with hEq | hAdj
  · have hLiftEq :
        (⟨e x.1,hxBlock⟩ : BlockFiber block b) =
          (⟨e y.1,hyBlock⟩ : BlockFiber block b) :=
      Subtype.ext (congrArg e hEq)
    exact False.elim (huv (hxu.symm.trans (hLiftEq.trans hyv)))
  · have huVal : u.1 = e x.1 :=
      (congrArg Subtype.val hxu).symm
    have hvVal : v.1 = e y.1 :=
      (congrArg Subtype.val hyv).symm
    rw [huVal,hvVal]
    exact (he x.1 y.1).mp hAdj

/-- Every block subtype has precisely the cardinality of the
corresponding host block fibre. -/
theorem blockFiber_card_eq_filter {W B : Type*}
    [Fintype W] [DecidableEq B]
    (block : W → B) (b : B) :
    Fintype.card (BlockFiber block b) =
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card := by
  classical
  simp [Fintype.card_subtype]

/-- Claim 3.13, Case 1: genuine EPPA plus unequal selected
block sizes and a nontrivial internal selected edge force every
host imprimitivity block to be a complete graph. -/
theorem eppa_case1_all_blocks_complete {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hOneEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hNotWhole : ∃ x y : V, block (e x) ≠ block (e y))
    (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (b c : B)
    (hDifferent :
      (selectedInBlock e block b).card ≠
        (selectedInBlock e block c).card) :
    ∀ j : B, ∀ u v : W, u ≠ v →
      block u = j → block v = j → H.Adj u v := by
  classical
  obtain ⟨b₀,hLarge⟩ :=
    unequal_selected_blocks_give_majority
      e block m hUniform hDouble b c hDifferent
  let S : Finset V := selectedInBlock e block b₀
  have hPositive : 0 < S.card := by
    change 0 < (selectedInBlock e block b₀).card
    omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hPositive
  have hxBlock : block (e x) = b₀ :=
    (Finset.mem_filter.mp hx).2
  let T : Finset (BlockFiber block b₀) :=
    selectedBlockPoints e block b₀
  have hTcard : T.card = S.card := by
    exact selectedBlockPoints_card e block b₀
  have hBcard : Fintype.card (BlockFiber block b₀) = m :=
    (blockFiber_card_eq_filter block b₀).trans (hUniform b₀)
  have hLargeS : m < 2 * S.card := by
    change m < 2 * (selectedInBlock e block b₀).card
    exact hLarge
  have hMajority : Fintype.card (BlockFiber block b₀) < 2 * T.card := by
    rw [hBcard, hTcard]
    exact hLargeS
  have hSame : ∀ y z : V,
      block (e y) = block (e z) ↔ y = z ∨ G.Adj y z :=
    eppa_base_same_block_iff_eq_or_adj
      G H e heppa block hBlocks hOneEdge hNotWhole
  have hClique :
      (inducedBlockGraph H block b₀).IsClique
        (T : Set (BlockFiber block b₀)) :=
    selectedBlockPoints_clique G H e heppa.1 block b₀ hSame
  exact all_blocks_complete_of_one_majority_clique
    H block hBlocks hTrans hSurj b₀
      (e x) hxBlock T hMajority hClique

end EPPAIII.BlockSystems
