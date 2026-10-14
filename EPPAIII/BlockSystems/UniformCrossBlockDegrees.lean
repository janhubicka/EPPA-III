import EPPAIII.BlockSystems.CrossBlockNeighbourCounts
import EPPAIII.BlockSystems.TransitivePartition

/-!
# Uniform per-target-block degrees in unequal-clique Case 1

Two-point EPPA implies that each selected vertex has the same
number r of neighbours into every *different occupied* block:
compare its ordered nonedge to an arbitrary selected vertex in
the target block against one fixed ordered selected nonedge.

Once all host blocks meet the selected copy, host vertex
transitivity transports the selected-vertex statement to every
host vertex. Since the quotient graph is complete, r is positive.

This supplies the independent cross-degree statement needed
for the double-counting part of Claim 3.15. The pairwise
equation k_i r = (m-k_j)r remains a separate finite counting step.
-/

namespace EPPAIII.BlockSystems

/-- Two-point EPPA gives a universal neighbour count r from each
selected vertex into every other host block, provided each block
is represented by a selected vertex. -/
theorem eppa_selected_cross_block_degree_uniform {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y)
    (hAllOccupied : ∀ j : B, j ∈ occupiedBlocks e block)
    (b c : B) (hb : b ∈ occupiedBlocks e block)
    (hc : c ∈ occupiedBlocks e block) (hbc : b ≠ c) :
    ∃ r : ℕ, ∀ x : V, ∀ j : B, block (e x) ≠ j →
      neighboursInBlock H block (e x) j = r := by
  classical
  obtain ⟨x₀,hx₀⟩ := (mem_occupiedBlocks e block b).mp hb
  obtain ⟨z₀,hz₀⟩ := (mem_occupiedBlocks e block c).mp hc
  have hDiff₀ : block (e x₀) ≠ block (e z₀) := by
    rw [hx₀,hz₀]
    exact hbc
  let r : ℕ := neighboursInBlock H block (e x₀) c
  refine ⟨r, ?_⟩
  intro x j hxj
  obtain ⟨z,hz⟩ :=
    (mem_occupiedBlocks e block j).mp (hAllOccupied j)
  have hDiff : block (e x) ≠ block (e z) := by
    rw [hz]
    exact hxj
  have hEq :=
    eppa_selected_block_neighbour_count_eq
      G H e heppa block hBlocks hSurj hSame
      x₀ z₀ x z hDiff₀ hDiff
  simpa only [hz₀,hz] using hEq.symm

/-- If every host block is occupied, vertex-transitivity transports
the selected uniform cross-block neighbour degree to all vertices. -/
theorem host_cross_block_degree_uniform {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hAllOccupied : ∀ j : B, j ∈ occupiedBlocks e block)
    (r : ℕ)
    (hSelected : ∀ x : V, ∀ j : B,
      block (e x) ≠ j → neighboursInBlock H block (e x) j = r) :
    ∀ u : W, ∀ j : B, block u ≠ j →
      neighboursInBlock H block u j = r := by
  classical
  intro u j huj
  obtain ⟨x,hx⟩ :=
    (mem_occupiedBlocks e block (block u)).mp
      (hAllOccupied (block u))
  obtain ⟨q,hq,hqmap⟩ := hTrans (e x) u
  let σ := liftBlockAutomorphism H block hBlocks hSurj q hq
  let k : B := σ.symm j
  have hσk : σ k = j := σ.apply_symm_apply j
  have hBlockX : block (e x) ≠ k := by
    intro heq
    have hBlockU : block u = j := by
      calc
        block u = block (q (e x)) := by rw [hqmap]
        _ = σ (block (e x)) :=
          (liftBlockAutomorphism_vertex
            H block hBlocks hSurj q hq (e x)).symm
        _ = σ k := by rw [heq]
        _ = j := hσk
    exact huj hBlockU
  have hTransport :=
    neighboursInBlock_aut H block hBlocks hSurj q hq (e x) k
  have hTransport' :
      neighboursInBlock H block (e x) k =
        neighboursInBlock H block u j := by
    change (liftBlockAutomorphism H block hBlocks hSurj q hq) k = j at hσk
    simpa only [hqmap, hσk] using hTransport
  exact hTransport'.symm.trans (hSelected x k hBlockX)

/-- A complete nontrivial block quotient forces the common
per-other-block neighbour degree to be positive. -/
theorem positive_common_cross_block_degree {W B : Type*}
    [Fintype W] [DecidableEq W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (block : W → B) (r : ℕ)
    (hUniform : ∀ u : W, ∀ j : B,
      block u ≠ j → neighboursInBlock H block u j = r)
    (hComplete : blockConnectionGraph H block = ⊤)
    (i j : B) (hij : i ≠ j) :
    0 < r := by
  classical
  have hEdge : (blockConnectionGraph H block).Adj i j := by
    rw [hComplete]
    exact hij
  obtain ⟨_,u,v,hu,hv,hAdj⟩ := hEdge
  have hPositive :
      0 < neighboursInBlock H block u j := by
    unfold neighboursInBlock
    apply Finset.card_pos.mpr
    exact ⟨v, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,⟨hv,hAdj⟩⟩⟩
  have hNe : block u ≠ j := by
    rw [hu]
    exact hij
  rw [hUniform u j hNe] at hPositive
  exact hPositive

end EPPAIII.BlockSystems
