import EPPAIII.BlockSystems.Claim314CrossEdges
import EPPAIII.BlockSystems.UnequalCliqueClaim313
import EPPAIII.BlockSystems.OccupiedBlockMajority
import EPPAIII.BlockSystems.UnequalCase1Arithmetic

/-!
# Case 1 of Lemma 3.12: at most one unoccupied block

With the actual block quotient complete, the cross-block
edge exclusion of Claim 3.14 prevents two different host
blocks from both being disjoint from G: their quotient edge
would have to be realised by two outside vertices.

In the unequal-clique Case 1 hypotheses, Claim 3.13
produces complete host blocks, and the genuine EPPA action
then forces the block quotient to be complete. Thus the
at-most-one-unoccupied statement is a *conclusion*, not
an assumption about an arbitrarily chosen partition.

The final exclusion of one remaining unoccupied block,
and the cross-degree and matching argument, remain separate.
-/

namespace EPPAIII.BlockSystems

/-- The two halves really give a bipartition of the cross-block
edge graph: an edge of H between distinct invariant blocks has
exactly one endpoint in the selected copy. -/
theorem cross_block_edges_are_mixed {V W B : Type*}
    [Fintype V] [Nonempty V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (he : IsInducedGraphEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y))
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (u v : W) (hCross : (crossBlockGraph H block).Adj u v) :
    (u ∈ Set.range e ∧ v ∉ Set.range e) ∨
      (u ∉ Set.range e ∧ v ∈ Set.range e) := by
  classical
  obtain ⟨hAdj,hDiff⟩ := hCross
  by_cases hu : u ∈ Set.range e
  · by_cases hv : v ∈ Set.range e
    · obtain ⟨x,rfl⟩ := hu
      obtain ⟨y,rfl⟩ := hv
      have hG : G.Adj x y := (he x y).mpr hAdj
      exact False.elim (hDiff (hSelectedInside x y hG))
    · exact Or.inl ⟨hu,hv⟩
  · by_cases hv : v ∈ Set.range e
    · exact Or.inr ⟨hu,hv⟩
    · have hSame : block u = block v :=
        no_outside_cross_block_edges G H e he
          block hBlocks hTrans hSelectedInside hDouble
          u v hu hv hAdj
      exact False.elim (hDiff hSame)


/-- A complete quotient admits at most one unoccupied block.
This uses the actual outside-outside exclusion, not a
postulated empty-empty edge condition. -/
theorem at_most_one_unoccupied_of_complete_quotient {V W B : Type*}
    [Fintype V] [Nonempty V] [Fintype W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj]
    (e : V ↪ W) (he : IsInducedGraphEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y))
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (hComplete : blockConnectionGraph H block = ⊤) :
    (occupiedBlocks e block)ᶜ.card ≤ 1 := by
  classical
  apply complete_quotient_at_most_one_unoccupied
    H block (occupiedBlocks e block) hComplete
  intro i j hi hj hij hEdge
  obtain ⟨_,u,v,hu,hv,huv⟩ := hEdge
  have huOutside : u ∉ Set.range e := by
    rintro ⟨x,hx⟩
    apply hi
    exact (mem_occupiedBlocks e block i).mpr
      ⟨x,by rw [hx]; exact hu⟩
  have hvOutside : v ∉ Set.range e := by
    rintro ⟨y,hy⟩
    apply hj
    exact (mem_occupiedBlocks e block j).mpr
      ⟨y,by rw [hy]; exact hv⟩
  have hSame : block u = block v :=
    no_outside_cross_block_edges G H e he
      block hBlocks hTrans hSelectedInside hDouble
      u v huOutside hvOutside huv
  exact hij (hu.symm.trans (hSame.trans hv))

/-- Under actual unequal-clique Case 1 hypotheses, all host
blocks are complete, the quotient graph is complete, and
there is at most one block missed by the selected copy.
None of these three conclusions is assumed. -/
theorem eppa_case1_quotient_and_unoccupied_bound {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [Fintype B] [Nonempty B] [DecidableEq B]
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
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (i j : B)
    (hi : i ∈ occupiedBlocks e block)
    (hj : j ∈ occupiedBlocks e block)
    (hDifferent :
      (selectedInBlock e block i).card ≠
        (selectedInBlock e block j).card) :
    (∀ b : B, ∀ u v : W, u ≠ v →
       block u = b → block v = b → H.Adj u v) ∧
    blockConnectionGraph H block = ⊤ ∧
      (occupiedBlocks e block)ᶜ.card ≤ 1 := by
  classical
  have hAllBlocks :
      ∀ b : B, ∀ u v : W, u ≠ v →
        block u = b → block v = b → H.Adj u v :=
    eppa_case1_all_blocks_complete
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hNotWhole m hUniform hDouble i j hDifferent
  have hComplete : blockConnectionGraph H block = ⊤ :=
    eppa_unequal_occupied_quotient_complete
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hAllBlocks hNonCluster m hUniform
      hDouble i j hi hj hDifferent
  have hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y) :=
    eppa_base_edges_internal_of_one G H e heppa
      block hBlocks hOneEdge
  have hAtMostOne :
      (occupiedBlocks e block)ᶜ.card ≤ 1 :=
    at_most_one_unoccupied_of_complete_quotient
      G H e heppa.1 block hBlocks hTrans
      hSelectedInside hDouble hComplete
  exact ⟨hAllBlocks,hComplete,hAtMostOne⟩

end EPPAIII.BlockSystems
