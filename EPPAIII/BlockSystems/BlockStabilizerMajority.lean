import EPPAIII.BlockSystems.OccupiedBlockAction
import EPPAIII.CliqueCovers.MajorityQuotientRigidity

/-!
# Block stabilisers and the majority-clique argument of Claim 3.13

An invariant system of imprimitivity has a genuine action on
its fibres. If a host automorphism takes u to v in the same block,
it preserves that block as a set, so the setwise stabiliser is
transitive on each block. Consequently every nonempty block induces
a regular graph.

The regular-majority-clique theorem implies that an induced clique
on more than half the vertices of a block forces that block to be
complete. Vertex transitivity transfers completeness to all blocks.

There is no coherence requirement on the automorphisms witnessing
transitivity. The separate Case-1 task is to produce the required
majority-sized selected clique from the unequal-clique assumptions.
-/

namespace EPPAIII.BlockSystems

/-- A vertex together with evidence that it lies in the block b. -/
abbrev BlockFiber {W B : Type*} (block : W → B) (b : B) :=
  {w : W // block w = b}

/-- The induced graph on a given block. -/
def inducedBlockGraph {W B : Type*}
    (H : SimpleGraph W) (block : W → B) (b : B) :
    SimpleGraph (BlockFiber block b) :=
  H.comap Subtype.val

/-- If two host vertices belong to the same invariant block,
a transitivity automorphism taking one to the other stabilises
their entire block setwise. -/
theorem transitive_block_stabiliser {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (u v : W) (hSame : block u = block v) :
    ∃ q : Equiv.Perm W,
      IsGraphAutomorphism H q ∧ q u = v ∧
      (∀ w : W, block w = block u ↔ block (q w) = block u) := by
  obtain ⟨q,hq,hqu⟩ := hTrans u v
  refine ⟨q,hq,hqu,?_⟩
  intro w
  have h := hBlocks q hq w u
  simpa only [hqu, ← hSame] using h

/-- Restrict any genuine host automorphism that preserves a block
to an actual permutation of the subtype of vertices in that block. -/
noncomputable def restrictBlockAutomorphism {W B : Type*}
    (block : W → B) (b : B)
    (q : Equiv.Perm W)
    (hPreserve : ∀ w : W,
      block w = b ↔ block (q w) = b) :
    Equiv.Perm (BlockFiber block b) where
  toFun x := ⟨q x.1, (hPreserve x.1).mp x.2⟩
  invFun x := ⟨q.symm x.1,
    (hPreserve (q.symm x.1)).mpr (by simpa using x.2)⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    simp

/-- The graph induced on each nonempty invariant block is
vertex-transitive under its actual graph automorphisms. -/
theorem induced_block_transitive {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (b : B) :
    CliqueCovers.HasTransitiveGraphAutomorphisms
      (inducedBlockGraph H block b) := by
  intro x y
  obtain ⟨q,hq,hxy,hSet⟩ :=
    transitive_block_stabiliser H block hBlocks hTrans
      x.1 y.1 (x.2.trans y.2.symm)
  have hPreserve : ∀ w : W,
      block w = b ↔ block (q w) = b := by
    intro w
    have h := hSet w
    simpa only [x.2] using h
  let σ := restrictBlockAutomorphism block b q hPreserve
  refine ⟨σ, ?_, ?_⟩
  · intro u v
    change H.Adj u.1 v.1 ↔ H.Adj (q u.1) (q v.1)
    exact hq u.1 v.1
  · apply Subtype.ext
    exact hxy

/-- A clique occupying more than half one invariant block
forces that entire block to induce the complete graph. -/
theorem induced_block_complete_of_majority_clique {W B : Type*}
    [Fintype W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj] (block : W → B) (b : B)
    (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (w : W) (hw : block w = b)
    (S : Finset (BlockFiber block b))
    (hMajority : Fintype.card (BlockFiber block b) < 2 * S.card)
    (hClique : (inducedBlockGraph H block b).IsClique (S : Set _)) :
    inducedBlockGraph H block b = ⊤ := by
  classical
  letI : Nonempty (BlockFiber block b) := ⟨⟨w, hw⟩⟩
  obtain ⟨d,hRegular⟩ :=
    CliqueCovers.regular_of_transitive_graph
      (inducedBlockGraph H block b)
      (induced_block_transitive H block hBlocks hTrans b)
  exact CliqueCovers.regular_majority_clique_eq_top
    (inducedBlockGraph H block b) d hRegular S hMajority hClique

/-- Reformulate completeness of a block's induced graph as
the concrete adjacency relation between its host vertices. -/
theorem block_complete_of_induced_top {W B : Type*}
    (H : SimpleGraph W) (block : W → B) (b : B)
    (hTop : inducedBlockGraph H block b = ⊤) :
    ∀ u v : W, u ≠ v → block u = b → block v = b →
      H.Adj u v := by
  intro u v huv hu hv
  have hDifferent :
      (⟨u,hu⟩ : BlockFiber block b) ≠ ⟨v,hv⟩ := by
    intro heq
    exact huv (congrArg Subtype.val heq)
  have hAdjTop :
      (⊤ : SimpleGraph (BlockFiber block b)).Adj ⟨u,hu⟩ ⟨v,hv⟩ :=
    hDifferent
  have hAdj : (inducedBlockGraph H block b).Adj
      ⟨u,hu⟩ ⟨v,hv⟩ := by
    rw [hTop]
    exact hAdjTop
  exact hAdj

/-- If one invariant block is complete, host transitivity
makes every other invariant block complete as well. -/
theorem complete_block_propagates {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSurj : Function.Surjective block)
    (b₀ : B)
    (hComplete : ∀ u v : W, u ≠ v →
      block u = b₀ → block v = b₀ → H.Adj u v) :
    ∀ b : B, ∀ u v : W, u ≠ v →
      block u = b → block v = b → H.Adj u v := by
  intro b u v huv hu hv
  obtain ⟨z,hz⟩ := hSurj b₀
  obtain ⟨q,hq,hzu⟩ := hTrans z u
  have hPreimage : block (q.symm v) = b₀ := by
    calc
      block (q.symm v) = block z :=
        (hBlocks q hq (q.symm v) z).mpr
          (by simpa [hzu] using (hv.trans hu.symm))
      _ = b₀ := hz
  have hDifferent : z ≠ q.symm v := by
    intro hEq
    apply huv
    calc
      u = q z := hzu.symm
      _ = q (q.symm v) := by rw [hEq]
      _ = v := by simp
  have hAdj := hComplete z (q.symm v) hDifferent hz hPreimage
  have hImg : H.Adj (q z) (q (q.symm v)) := (hq _ _).mp hAdj
  simpa only [hzu, q.apply_symm_apply] using hImg

/-- Claim 3.13's structural step: a majority clique in one
block forces all blocks of a transitive invariant partition
to induce complete graphs. -/
theorem all_blocks_complete_of_one_majority_clique {W B : Type*}
    [Fintype W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj] (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSurj : Function.Surjective block)
    (b₀ : B) (w : W) (hw : block w = b₀)
    (S : Finset (BlockFiber block b₀))
    (hMajority : Fintype.card (BlockFiber block b₀) < 2 * S.card)
    (hClique : (inducedBlockGraph H block b₀).IsClique (S : Set _)) :
    ∀ b : B, ∀ u v : W, u ≠ v →
      block u = b → block v = b → H.Adj u v := by
  have hTop := induced_block_complete_of_majority_clique
    H block b₀ hBlocks hTrans w hw S hMajority hClique
  exact complete_block_propagates
    H block hBlocks hTrans hSurj b₀
    (block_complete_of_induced_top H block b₀ hTop)

end EPPAIII.BlockSystems
