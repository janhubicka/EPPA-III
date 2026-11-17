import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-!
# The exceptional bilinear cover parameters

The complement of the second subconstituent in the parameter case
`(m,q) = (3,2)` has order 42 and degree 26. Its cover parameters
are constrained by the generalised clique-cover degree formula.
-/

namespace EPPAIII.Primitive

/-- For a cover with two halves of size 21 and degree 26, the matched
blocks have size 7, diagonal cross edges omit a matching, and
off-diagonal cross edges are complete. -/
theorem bilinear_3_2_cover_parameters (s t c : Nat) (Y : Bool)
    (hSize : s * t = 21)
    (hCross : c = 0 ∨ c = t ∨ c = 1 ∨ c = t - 1)
    (hDegree : t - 1 + c + (if Y then (s - 1) * t else 0) = 26) :
    s = 3 ∧ t = 7 ∧ c = t - 1 ∧ Y = true := by
  have hs : 0 < s := Nat.pos_of_ne_zero (fun h => by simp [h] at hSize)
  have ht : 0 < t := Nat.pos_of_ne_zero (fun h => by simp [h] at hSize)
  have htLe : t ≤ 21 := Nat.le_of_dvd (by decide) ⟨s, by rw [Nat.mul_comm, hSize]⟩
  cases Y with
  | false =>
      simp at hDegree
      have hcLe : c ≤ t := by
        rcases hCross with h0 | hT | h1 | hBar <;> omega
      have hsOne : s = 1 := by
        by_cases h : s = 1
        · exact h
        · have hTwo : 2 ≤ s := by omega
          have hTwice := Nat.mul_le_mul_right t hTwo
          rw [hSize] at hTwice
          omega
      have ht21 : t = 21 := by simpa [hsOne] using hSize
      rcases hCross with h0 | hT | h1 | hBar <;> omega
  | true =>
      simp at hDegree
      have hAcross : (s - 1) * t = 21 - t := by
        rw [Nat.sub_mul, hSize, Nat.one_mul]
      have hcSix : c = 6 := by omega
      rcases hCross with h0 | hT | h1 | hBar
      · omega
      · have htSix : t = 6 := by omega
        rw [htSix] at hSize
        omega
      · omega
      · have htSeven : t = 7 := by omega
        have hsThree : s = 3 := by
          rw [htSeven] at hSize
          omega
        exact ⟨hsThree, htSeven, hBar, rfl⟩

end EPPAIII.Primitive
