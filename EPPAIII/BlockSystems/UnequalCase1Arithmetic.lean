import EPPAIII.BlockSystems.OccupiedBlockMajority

/-!
# Cardinality reductions at the end of Case 1 of Lemma 3.12

Two elementary consequences of Claim 3.14's proposed edge-count
argument are recorded independently of how that claim is established:

* If positive selected block sizes satisfy k_i+k_j=m for every
  distinct occupied pair and are not all equal, there can be only
  two occupied blocks.
* If the actual quotient graph on blocks is complete, and there
  are no edges between distinct unoccupied blocks, there is at
  most one unoccupied block.

The first argument is a three-index contradiction, not a graph
classification; the second is a direct use of quotient completeness.
This module deliberately does not assert that the hypotheses
follow from EPPA without the remaining Claim 3.14 proof.
-/

namespace EPPAIII.BlockSystems

/-- Pairwise complementary occupancy sizes cannot vary across
three or more occupied blocks. -/
theorem complementary_unequal_sizes_exactly_two {B : Type*}
    [DecidableEq B]
    (S : Finset B) (k : B → ℕ) (m : ℕ)
    (hPair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → k i + k j = m)
    (hDifferent : ∃ i ∈ S, ∃ j ∈ S, k i ≠ k j) :
    S.card = 2 := by
  classical
  obtain ⟨a,ha,b,hb,hUnequal⟩ := hDifferent
  have hab : a ≠ b := by
    intro h
    subst b
    exact hUnequal rfl
  have hExact : S = {a,b} := by
    apply Finset.Subset.antisymm
    · intro x hx
      by_contra hxnot
      have hxa : x ≠ a := by
        intro h
        apply hxnot
        simp [h]
      have hxb : x ≠ b := by
        intro h
        apply hxnot
        simp [h]
      have hA : k x + k a = m := hPair x hx a ha hxa
      have hB : k x + k b = m := hPair x hx b hb hxb
      have : k a = k b := by omega
      exact hUnequal this
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
  rw [hExact]
  simp [hab]

/-- Specialized to the actual occupied blocks of an EPPA host.
This is only the last arithmetic step once Claim 3.14 has supplied
the pairwise complementary selected occupancy equation. -/
theorem eppa_occupied_complementary_unequal_exactly_two {V W B : Type*}
    [Fintype V] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (m : ℕ)
    (hPair : ∀ i ∈ occupiedBlocks e block,
      ∀ j ∈ occupiedBlocks e block, i ≠ j →
        (selectedInBlock e block i).card +
          (selectedInBlock e block j).card = m)
    (hDifferent : ∃ i ∈ occupiedBlocks e block,
      ∃ j ∈ occupiedBlocks e block,
        (selectedInBlock e block i).card ≠
          (selectedInBlock e block j).card) :
    (occupiedBlocks e block).card = 2 := by
  exact complementary_unequal_sizes_exactly_two
    (occupiedBlocks e block)
    (fun i => (selectedInBlock e block i).card) m
    hPair hDifferent

/-- Completeness of the actual quotient, together with the
Claim 3.14 empty-empty edge exclusion, leaves at most one
block disjoint from the selected copy. -/
theorem complete_quotient_at_most_one_unoccupied {W B : Type*}
    [Fintype B] [DecidableEq B]
    (H : SimpleGraph W) (block : W → B)
    (S : Finset B)
    (hComplete : blockConnectionGraph H block = ⊤)
    (hNoUnselectedEdges : ∀ i j : B, i ∉ S → j ∉ S →
      i ≠ j → ¬ (blockConnectionGraph H block).Adj i j) :
    (Sᶜ).card ≤ 1 := by
  classical
  by_contra hTooMany
  have hTwo : 1 < (Sᶜ).card := by omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hTwo
  have hiOut : i ∉ S := by simpa using hi
  have hjOut : j ∉ S := by simpa using hj
  have hEdge : (blockConnectionGraph H block).Adj i j := by
    rw [hComplete]
    exact hij
  exact hNoUnselectedEdges i j hiOut hjOut hij hEdge

/-- If all host blocks are occupied and the pairwise cross-edge
degree equation holds, there are precisely two host blocks. -/
theorem all_occupied_complementary_unequal_two_blocks {B : Type*}
    [Fintype B] [DecidableEq B]
    (k : B → ℕ) (m : ℕ)
    (hPair : ∀ i j : B, i ≠ j → k i + k j = m)
    (hDifferent : ∃ i j : B, k i ≠ k j) :
    Fintype.card B = 2 := by
  classical
  have hPair' : ∀ i ∈ (Finset.univ : Finset B),
      ∀ j ∈ (Finset.univ : Finset B),
      i ≠ j → k i + k j = m := by
    intro i _ j _ hij
    exact hPair i j hij
  have hDiff' : ∃ i ∈ (Finset.univ : Finset B),
      ∃ j ∈ (Finset.univ : Finset B),
      k i ≠ k j := by
    obtain ⟨i,j,hij⟩ := hDifferent
    exact ⟨i,Finset.mem_univ _,j,Finset.mem_univ _,hij⟩
  simpa using complementary_unequal_sizes_exactly_two
    (Finset.univ : Finset B) k m hPair' hDiff'

end EPPAIII.BlockSystems
