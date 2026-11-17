import EPPAIII.Primitive.SmallConstituentTable
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# The two constituent profiles of the alternating forms graph A(5,q)

The SRG parameters are those of Brouwer–Van Maldeghem §3.4.2. The
arithmetic below supports the sparse-degree exclusion of clique unions,
generalised clique covers, and their complements.
-/

namespace EPPAIII.Primitive

/-- Strongly regular parameters of the alternating forms graph A(5,q). -/
def alternatingFiveParameters (q : Nat) : SRGParameters :=
  ⟨q ^ 10, (q ^ 2 + 1) * (q ^ 5 - 1),
    q ^ 5 + q ^ 4 - q ^ 2 - 2, q ^ 2 * (q ^ 2 + 1)⟩

private theorem power_le {q a b : Nat} (hq : 0 < q) (hab : a ≤ b) : q ^ a ≤ q ^ b :=
  Nat.pow_le_pow_right hq hab

private theorem mul_power_le {q a b c : Nat} (hc : c ≤ q ^ b) :
    c * q ^ a ≤ q ^ (b + a) := by
  rw [Nat.pow_add]
  exact Nat.mul_le_mul_right _ hc

private theorem alternatingFive_first_sparse_of_three {q : Nat} (hq : 3 ≤ q) :
    let p := (alternatingFiveParameters q).constituentProfile false
    1 < p.2 ∧ 2 * p.2 + 2 < p.1 ∧ 4 * p.2 < p.1 := by
  dsimp [alternatingFiveParameters, SRGParameters.constituentProfile]
  have hPositive : 0 < q := by omega
  have h4Pos : 0 < q ^ 4 := Nat.pow_pos hPositive
  have h3 : 3 * q ^ 4 ≤ q ^ 5 := mul_power_le (a := 4) (b := 1)
    (by simpa only [Nat.pow_one] using hq)
  have h4 := power_le (a := 2) (b := 4) hPositive (by decide)
  have hq5 : 3 ^ 5 ≤ q ^ 5 := Nat.pow_le_pow_left hq 5
  have hq2 : 3 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hK : 9 * (q ^ 5 - 1) ≤ (q ^ 2 + 1) * (q ^ 5 - 1) :=
    Nat.mul_le_mul_right (q ^ 5 - 1) (by omega)
  omega

/-- The first constituent at q = 2 has odd order. For q ≥ 3 its degree
is below one quarter of its order. In all cases it is connected-sparse
in the sense used by the clique-cover exclusion. -/
theorem alternatingFive_first_sparse {q : Nat} (hq : 2 ≤ q) :
    let p := (alternatingFiveParameters q).constituentProfile false
    1 < p.2 ∧ 2 * p.2 + 2 < p.1 ∧ (p.1 % 2 = 1 ∨ 4 * p.2 < p.1) := by
  by_cases hTwo : q = 2
  · subst q
    decide
  · have h := alternatingFive_first_sparse_of_three (q := q) (by omega)
    exact ⟨h.1, h.2.1, Or.inr h.2.2⟩

/-- The second constituent has degree below one quarter of its order
for every field order. The degree is greater than one. -/
theorem alternatingFive_second_sparse {q : Nat} (hq : 2 ≤ q) :
    let p := (alternatingFiveParameters q).constituentProfile true
    1 < p.2 ∧ 2 * p.2 + 2 < p.1 ∧ 4 * p.2 < p.1 := by
  dsimp [alternatingFiveParameters, SRGParameters.constituentProfile]
  have hq2 : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hq3 : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hq7 : 2 ^ 7 ≤ q ^ 7 := Nat.pow_le_pow_left hq 7
  have h5 : 8 * q ^ 2 ≤ q ^ 5 := mul_power_le (a := 2) (b := 3) hq3
  have h7 : 4 * q ^ 5 ≤ q ^ 7 := mul_power_le (a := 5) (b := 2) hq2
  have h10 : 8 * q ^ 7 ≤ q ^ 10 := mul_power_le (a := 7) (b := 3) hq3
  have hKUpper : (q ^ 2 + 1) * (q ^ 5 - 1) ≤ q ^ 7 + q ^ 5 := by
    calc
      _ ≤ (q ^ 2 + 1) * q ^ 5 := Nat.mul_le_mul_left _ (Nat.sub_le ..)
      _ = _ := by rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add]
  have hL := Nat.mul_le_mul_left (q ^ 2 + 1) (show q ^ 2 + 2 ≤ q ^ 5 - 1 by omega)
  rw [Nat.mul_add, Nat.mul_comm (q ^ 2 + 1) (q ^ 2), Nat.mul_comm _ 2] at hL
  omega

/-- A uniform arithmetic conclusion for either constituent. -/
theorem alternatingFive_constituent_sparse {q : Nat} (hq : 2 ≤ q) (side : Bool) :
    let p := (alternatingFiveParameters q).constituentProfile side
    1 < p.2 ∧ 2 * p.2 + 2 < p.1 ∧ (p.1 % 2 = 1 ∨ 4 * p.2 < p.1) := by
  cases side
  · exact alternatingFive_first_sparse hq
  · have h := alternatingFive_second_sparse hq
    exact ⟨h.1, h.2.1, Or.inr h.2.2⟩

private theorem not_dvd_of_between_multiples {n t a : Nat}
    (hLower : t * a < n) (hUpper : n < t * (a + 1)) : ¬ t ∣ n := by
  rintro ⟨b, rfl⟩
  by_cases h : b ≤ a
  · have := Nat.mul_le_mul_left t h
    omega
  · have := Nat.mul_le_mul_left t (show a + 1 ≤ b by omega)
    omega

private theorem first_division {q : Nat} (hq : 2 ≤ q) :
    let p := (alternatingFiveParameters q).constituentProfile false
    let a := q ^ 2 - q + 1
    let r := q ^ 5 - q ^ 3 + (q ^ 2 - q)
    p.1 = (p.2 + 1) * a + r ∧ a < r ∧ r + a < p.2 := by
  dsimp [alternatingFiveParameters, SRGParameters.constituentProfile]
  have hPositive : 0 < q := by omega
  have hq2 := power_le (a := 1) (b := 2) hPositive (by decide)
  rw [Nat.pow_one] at hq2
  have hq4 := power_le (a := 2) (b := 4) hPositive (by decide)
  have hq3 : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have hq5 : 2 ^ 5 ≤ q ^ 5 := Nat.pow_le_pow_left hq 5
  have hq2Four : 4 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h5 : 4 * q ^ 3 ≤ q ^ 5 := mul_power_le (a := 3) (b := 2) hq2Four
  have h4 : 4 * q ^ 2 ≤ q ^ 4 := mul_power_le (a := 2) (b := 2) hq2Four
  refine ⟨?_, by omega, by omega⟩
  zify [show 1 ≤ q ^ 5 by omega,
    show q ^ 2 ≤ q ^ 5 + q ^ 4 by omega,
    show 2 ≤ q ^ 5 + q ^ 4 - q ^ 2 by omega,
    show q ^ 3 ≤ q ^ 5 by omega, hq2]
  ring

private theorem second_division {q : Nat} (hq : 2 ≤ q) :
    let p := (alternatingFiveParameters q).constituentProfile true
    let a := q ^ 3 - q
    let r := q ^ 6 - q ^ 3 + (q ^ 2 - q)
    p.1 = p.2 * a + r ∧ 2 * a < r ∧ r < p.2 := by
  have hsparse := alternatingFive_second_sparse hq
  dsimp [alternatingFiveParameters, SRGParameters.constituentProfile] at *
  have hPositive : 0 < q := by omega
  have hq2 := power_le (a := 1) (b := 2) hPositive (by decide)
  have hq3 := power_le (a := 1) (b := 3) hPositive (by decide)
  rw [Nat.pow_one] at hq2 hq3
  have hq5 : 2 ^ 5 ≤ q ^ 5 := Nat.pow_le_pow_left hq 5
  have hq2Four : 4 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have hq3Eight : 8 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h5 : 8 * q ^ 2 ≤ q ^ 5 := mul_power_le (a := 2) (b := 3) hq3Eight
  have h6 : 8 * q ^ 3 ≤ q ^ 6 := mul_power_le (a := 3) (b := 3) hq3Eight
  have h4 : 4 * q ^ 2 ≤ q ^ 4 := mul_power_le (a := 2) (b := 2) hq2Four
  have h5four : 2 * q ^ 4 ≤ q ^ 5 := mul_power_le (a := 4) (b := 1)
    (by simpa only [Nat.pow_one] using hq)
  have h7 := power_le (a := 6) (b := 7) hPositive (by decide)
  have hKLower : q ^ 2 * (q ^ 2 + 1) ≤ (q ^ 2 + 1) * (q ^ 5 - 1) := by
    rw [Nat.mul_comm (q ^ 2)]
    exact Nat.mul_le_mul_left _ (by omega)
  have hNLower : (q ^ 2 + 1) * (q ^ 5 - 1) ≤ q ^ 10 := by omega
  have hNPositive : 1 ≤ q ^ 10 - (q ^ 2 + 1) * (q ^ 5 - 1) := by omega
  have hK : (q ^ 2 + 1) * (q ^ 5 - 1) + q ^ 2 + 1 = q ^ 7 + q ^ 5 := by
    zify [show 1 ≤ q ^ 5 by omega]
    ring
  have hMu : q ^ 2 * (q ^ 2 + 1) = q ^ 4 + q ^ 2 := by ring
  refine ⟨?_, by omega, by omega⟩
  zify [show 1 ≤ q ^ 5 by omega, hKLower, hNLower, hNPositive,
    show q ^ 3 ≤ q ^ 6 by omega, hq2, hq3]
  ring

/-- No possible size of a clique block, or of two such blocks, divides the
order of either constituent of A(5,q). -/
theorem alternatingFive_constituent_near_degree_not_dvd {q : Nat} (hq : 2 ≤ q)
    (side : Bool) :
    let p := (alternatingFiveParameters q).constituentProfile side
    ¬ p.2 ∣ p.1 ∧ ¬ (p.2 + 1) ∣ p.1 ∧ ¬ (p.2 + 2) ∣ p.1 := by
  generalize hProfile : (alternatingFiveParameters q).constituentProfile side = p
  dsimp
  rcases p with ⟨n, d⟩
  dsimp
  cases side
  · have h := first_division hq
    rw [hProfile] at h
    dsimp at h
    rcases h with ⟨hIdentity, hRLower, hRUpper⟩
    refine ⟨?_, ?_, ?_⟩
    · apply not_dvd_of_between_multiples (a := q ^ 2 - q + 1)
      · rw [Nat.add_mul, Nat.one_mul] at hIdentity
        omega
      · rw [Nat.mul_add, Nat.mul_one]
        rw [Nat.add_mul, Nat.one_mul] at hIdentity
        omega
    · apply not_dvd_of_between_multiples (a := q ^ 2 - q + 1)
      · omega
      · rw [Nat.mul_add, Nat.mul_one]
        omega
    · apply not_dvd_of_between_multiples (a := q ^ 2 - q + 1)
      · simp only [Nat.add_mul, Nat.one_mul] at hIdentity ⊢
        omega
      · simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul] at hIdentity ⊢
        omega
  · have h := second_division hq
    rw [hProfile] at h
    dsimp at h
    rcases h with ⟨hIdentity, hRLower, hRUpper⟩
    refine ⟨?_, ?_, ?_⟩
    · apply not_dvd_of_between_multiples (a := q ^ 3 - q)
      · omega
      · rw [Nat.mul_add, Nat.mul_one]
        omega
    · apply not_dvd_of_between_multiples (a := q ^ 3 - q)
      · rw [Nat.add_mul, Nat.one_mul]
        omega
      · simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]
        omega
    · apply not_dvd_of_between_multiples (a := q ^ 3 - q)
      · rw [Nat.add_mul]
        omega
      · simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul]
        omega

end EPPAIII.Primitive
