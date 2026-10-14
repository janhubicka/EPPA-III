import EPPAIII.BlockSystems.CrossDegreeOne
import EPPAIII.BlockSystems.UnequalCase1TwoBlocks

/-!
# Actual unequal-clique Case-1 EPPA hypotheses force r = 1

The previous theorem establishes that, for two invariant blocks
with unequal complementary selected sizes, the common cross-block
degree cannot be >=2. We now remove every auxiliary assumption
from that statement using the actual double-sized transitive
EPPA embedding.

The host has exactly two blocks, both occupied by G, and every
cross-block edge joins one selected and one outside vertex.
Two-point EPPA makes the per-block degree uniform, and
double-counting proves that the selected sizes sum to the common
block size. The connected-component contradiction then yields
r=1.

This is the final mathematical content of the Case-1 reduction,
before spelling out that cross-degree one is a perfect matching.
-/

namespace EPPAIII.BlockSystems

/-- Any two distinct labels exhaust a finite type of order two. -/
theorem labels_exhaust_card_two {B : Type*}
    [Fintype B] [DecidableEq B]
    (i j : B) (hij : i ≠ j)
    (hCard : Fintype.card B = 2) :
    ∀ b : B, b = i ∨ b = j := by
  classical
  have hPairCard : ({i,j} : Finset B).card = 2 := by
    simp [hij]
  have hSubset : ({i,j} : Finset B) ⊆ Finset.univ :=
    Finset.subset_univ _
  have hCardLe :
      (Finset.univ : Finset B).card ≤ ({i,j} : Finset B).card := by
    calc
      (Finset.univ : Finset B).card = 2 := by simpa using hCard
      _ = ({i,j} : Finset B).card := hPairCard.symm
  have hUniverse : ({i,j} : Finset B) = Finset.univ :=
    Finset.eq_of_subset_of_card_le hSubset hCardLe
  intro b
  have hb : b ∈ ({i,j} : Finset B) := by
    rw [hUniverse]
    exact Finset.mem_univ _
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hb

/-- Complete Case-1 cross-degree conclusion starting solely
from an actual double-size vertex-transitive EPPA embedding
and a nontrivial invariant block system with unequal selected
clique sizes. -/
theorem eppa_case1_cross_degree_eq_one {V W B : Type*}
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
    ∃ r : ℕ, r = 1 ∧
      (∀ u : W, ∀ j : B, block u ≠ j →
        neighboursInBlock H block u j = r) := by
  classical
  have hbc : b ≠ c := by
    intro h
    subst c
    exact hDifferent rfl
  have hTwoBlocks : Fintype.card B = 2 :=
    eppa_case1_exactly_two_host_blocks
      G H e heppa block hBlocks hSurj hTrans hOneEdge
      hNotWhole hNonCluster m hUniformSize hDouble
      b c hb hc hDifferent
  have hTwoLabels : ∀ j : B, j = b ∨ j = c :=
    labels_exhaust_card_two b c hbc hTwoBlocks
  have hOccupied : occupiedBlocks e block = Finset.univ :=
    eppa_case1_all_host_blocks_occupied
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hNotWhole hNonCluster m
      hUniformSize hDouble b c hb hc hDifferent
  have hAllOccupied : ∀ j : B, j ∈ occupiedBlocks e block := by
    intro j
    rw [hOccupied]
    exact Finset.mem_univ _
  have hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y :=
    eppa_base_same_block_iff_eq_or_adj
      G H e heppa block hBlocks hOneEdge hNotWhole
  obtain ⟨r,hSelectedDegree⟩ :=
    eppa_selected_cross_block_degree_uniform
      G H e heppa block hBlocks hSurj hSame
      hAllOccupied b c hb hc hbc
  have hDegree : ∀ u : W, ∀ j : B, block u ≠ j →
      neighboursInBlock H block u j = r :=
    host_cross_block_degree_uniform
      H e block hBlocks hSurj hTrans
      hAllOccupied r hSelectedDegree
  obtain ⟨_,hQuotient,_⟩ :=
    eppa_case1_quotient_and_unoccupied_bound
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hNotWhole hNonCluster m hUniformSize
      hDouble b c hb hc hDifferent
  have hr : 0 < r :=
    positive_common_cross_block_degree
      H block r hDegree hQuotient b c hbc
  have hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y) :=
    eppa_base_edges_internal_of_one
      G H e heppa block hBlocks hOneEdge
  have hOutsideInside : ∀ u v : W,
      u ∉ Set.range e → v ∉ Set.range e →
      H.Adj u v → block u = block v := by
    intro u v hu hv huv
    exact no_outside_cross_block_edges
      G H e heppa.1 block hBlocks hTrans
      hSelectedInside hDouble u v hu hv huv
  have hMixed : ∀ u v : W,
      (crossBlockGraph H block).Adj u v →
        (u ∈ Set.range e ∧ v ∉ Set.range e) ∨
        (u ∉ Set.range e ∧ v ∈ Set.range e) :=
    cross_block_edges_are_mixed G H e heppa.1
      block hBlocks hTrans hSelectedInside hDouble
  have hComplement :
      (selectedInBlock e block b).card +
        (selectedInBlock e block c).card = m :=
    selected_occupied_pairwise_complementary
      G H e heppa.1 block hSelectedInside hOutsideInside
      m hUniformSize r hr hDegree b c hbc
  have hOne : r = 1 :=
    unequal_two_block_cross_degree_eq_one
      G H e heppa block hBlocks hTrans hSame
      hOutsideInside hMixed b c hbc hTwoLabels hb hc
      m hUniformSize hComplement hDifferent r hr hDegree
  exact ⟨r,hOne,hDegree⟩

end EPPAIII.BlockSystems
