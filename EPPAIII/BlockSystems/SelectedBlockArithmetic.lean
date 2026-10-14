import EPPAIII.BlockSystems.OccupiedBlockMajority

/-!
# Unequal selected block sizes force a majority clique candidate

In a uniform block partition, if the distinguished base occupies
exactly half the host vertices, the average number of selected
vertices per block is precisely half the block size.
If two block fibre sizes differ, one fibre must contain strictly
more than half its vertices from the base.

This isolates the numerical inference of Claim 3.13 from the
graph-theoretic stabiliser and majority-clique arguments.
-/

namespace EPPAIII.BlockSystems

/-- For a finite family of integer-valued nonnegative counts whose
mean is m/2, nonconstant counts force some entry above m/2. -/
theorem nonconstant_half_mean_has_large_entry {B : Type*}
    [Fintype B] (k : B → ℕ) (m : ℕ)
    (hHalf : (∑ b : B, 2 * k b) = Fintype.card B * m)
    (hDifferent : ∃ b c : B, k b ≠ k c) :
    ∃ b : B, m < 2 * k b := by
  classical
  by_contra hNone
  have hLe (b : B) : 2 * k b ≤ m := by
    by_contra hBad
    exact hNone ⟨b, by omega⟩
  obtain ⟨b,c,hDifferent⟩ := hDifferent
  have hStrict : 2 * k b < m ∨ 2 * k c < m := by
    have hB := hLe b
    have hC := hLe c
    omega
  obtain ⟨d,hd⟩ : ∃ d : B, 2 * k d < m := by
    rcases hStrict with hb | hc
    · exact ⟨b,hb⟩
    · exact ⟨c,hc⟩
  have hSumLt :
      (∑ x : B, 2 * k x) < (∑ _x : B, m) := by
    apply Finset.sum_lt_sum
    · intro x _
      exact hLe x
    · exact ⟨d,Finset.mem_univ _,hd⟩
  have hConst : (∑ _x : B, m) = Fintype.card B * m := by
    simp
  omega

/-- The numbers of selected vertices in all host blocks sum
to the number of vertices of the distinguished base graph. -/
theorem selectedInBlock_sum {V W B : Type*}
    [Fintype V] [Fintype B] [DecidableEq B]
    (e : V ↪ W) (block : W → B) :
    (∑ b : B, (selectedInBlock e block b).card) =
      Fintype.card V := by
  classical
  simpa [selectedInBlock] using
    (Finset.sum_fiberwise
      (Finset.univ : Finset V)
      (fun x : V => block (e x)) (fun _ => (1 : ℕ)))

/-- The double-sized host and uniform block sizes yield the
exact half-average identity on the selected fibre counts. -/
theorem selectedInBlock_double_sum {V W B : Type*}
    [Fintype V] [Fintype W] [Fintype B] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V) :
    (∑ b : B, 2 * (selectedInBlock e block b).card) =
      Fintype.card B * m := by
  classical
  have hSum :
      (∑ b : B, 2 * (selectedInBlock e block b).card) =
        2 * Fintype.card V := by
    calc
      (∑ b : B, 2 * (selectedInBlock e block b).card) =
          2 * (∑ b : B, (selectedInBlock e block b).card) := by
            rw [Finset.mul_sum]
      _ = 2 * Fintype.card V := by rw [selectedInBlock_sum]
  exact hSum.trans
    ((uniform_partition_card_formula block m hUniform).trans hDouble).symm

/-- The actual Case-1 arithmetic conclusion: unequal selected
occupancy counts force one block to contain strictly more than
half its vertices from the base graph. -/
theorem unequal_selected_blocks_give_majority {V W B : Type*}
    [Fintype V] [Fintype W] [Fintype B] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (b c : B)
    (hDifferent :
      (selectedInBlock e block b).card ≠
        (selectedInBlock e block c).card) :
    ∃ b₀ : B, m < 2 * (selectedInBlock e block b₀).card := by
  apply nonconstant_half_mean_has_large_entry
    (fun x : B => (selectedInBlock e block x).card) m
    (selectedInBlock_double_sum e block m hUniform hDouble)
  exact ⟨b,c,hDifferent⟩

end EPPAIII.BlockSystems
