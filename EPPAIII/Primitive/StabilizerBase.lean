import Mathlib.Data.Nat.Log
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Push

/-!
# Finite stabilizer chains

At every step where the current stabilizer moves an allowed point, fixing that
point cuts its order by at least two. This is the counting step in the
semilinear stabilizer argument.
-/

namespace EPPAIII.Primitive

variable {A X : Type*} [Group A] [Finite A] [MulAction A X]

/-- Fixing at most `log₂ |K|` points from a set suffices to force an element of
`K` to fix the entire set pointwise. -/
theorem exists_stabilizer_base_within (K : Subgroup A) (S : Set X) :
    ∃ U : Finset X, (U : Set X) ⊆ S ∧ U.card ≤ Nat.log 2 (Nat.card K) ∧
      ∀ g ∈ K, (∀ u ∈ U, g • u = u) → ∀ x ∈ S, g • x = x := by
  classical
  suffices hPower : ∀ K : Subgroup A,
      ∃ U : Finset X, (U : Set X) ⊆ S ∧ 2 ^ U.card ≤ Nat.card K ∧
        ∀ g ∈ K, (∀ u ∈ U, g • u = u) → ∀ x ∈ S, g • x = x by
    obtain ⟨U, hU, hSize, hFix⟩ := hPower K
    exact ⟨U, hU, Nat.le_log_of_pow_le (by decide) hSize, hFix⟩
  suffices hAll : ∀ n : ℕ, ∀ K : Subgroup A, Nat.card K = n →
      ∃ U : Finset X, (U : Set X) ⊆ S ∧ 2 ^ U.card ≤ Nat.card K ∧
        ∀ g ∈ K, (∀ u ∈ U, g • u = u) → ∀ x ∈ S, g • x = x by
    exact fun K => hAll (Nat.card K) K rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K hn
    by_cases hFixed : ∀ g ∈ K, ∀ x ∈ S, g • x = x
    · exact ⟨∅, by simp, by rw [Finset.card_empty, pow_zero]; exact Nat.card_pos,
        fun g hg _ => hFixed g hg⟩
    push Not at hFixed
    obtain ⟨g, hg, x, hx, hMove⟩ := hFixed
    let L : Subgroup A := K ⊓ MulAction.stabilizer A x
    have hLe : L ≤ K := inf_le_left
    have hProper : L.subgroupOf K ≠ ⊤ := by
      intro hTop
      exact hMove ((Subgroup.subgroupOf_eq_top.mp hTop hg).2)
    have hIndex := Subgroup.one_lt_index_of_ne_top hProper
    have hCard := (L.subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLe).toEquiv] at hCard
    have hHalves : Nat.card L * 2 ≤ Nat.card K := by
      rw [← hCard]
      exact Nat.mul_le_mul_left _ hIndex
    have hSmall : Nat.card L < n := by
      have hPos : 0 < Nat.card L := Nat.card_pos
      omega
    obtain ⟨U, hU, hSize, hFix⟩ := ih (Nat.card L) hSmall L rfl
    refine ⟨insert x U, ?_, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hx
      · exact hU hv
    · calc
        2 ^ (insert x U).card ≤ 2 ^ (U.card + 1) :=
          Nat.pow_le_pow_right (by decide) (Finset.card_insert_le x U)
        _ = 2 ^ U.card * 2 := by rw [pow_succ]
        _ ≤ Nat.card L * 2 := Nat.mul_le_mul_right _ hSize
        _ ≤ Nat.card K := hHalves
    · intro a ha hA
      have hAL : a ∈ L := ⟨ha, hA x (Finset.mem_insert_self x U)⟩
      exact hFix a hAL (fun u hu => hA u (Finset.mem_insert_of_mem hu))

end EPPAIII.Primitive
