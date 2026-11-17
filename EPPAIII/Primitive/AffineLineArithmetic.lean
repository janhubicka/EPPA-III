/-! # Prime powers below the two-anchor size bound -/

namespace EPPAIII.Primitive

/-- Above the initial exponent, a power of base at least two grows faster
than the two-anchor affine line bound. -/
private theorem affineBound_lt_pow {p s r : Nat} (hp : 2 ≤ p) (hs : 1 ≤ s)
    (hsr : s ≤ r) (hStart : 8 * s + 4 < p ^ s) : 8 * r + 4 < p ^ r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsr
  clear hsr
  induction d with
  | zero => simpa using hStart
  | succ d ih =>
    change 8 * (s + d + 1) + 4 < p ^ (s + d + 1)
    rw [Nat.pow_succ p (s + d)]
    have hs' : 1 ≤ s + d := Nat.le_trans hs (Nat.le_add_right s d)
    have hAdd : 8 ≤ 8 * (s + d) + 4 :=
      Nat.add_le_add_right
        (Nat.le_trans (by decide : 4 ≤ 8 * 1) (Nat.mul_le_mul_left 8 hs')) 4
    calc
      8 * (s + d + 1) + 4 = (8 * (s + d) + 4) + 8 := by
        simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      _ ≤ (8 * (s + d) + 4) + (8 * (s + d) + 4) := Nat.add_le_add_left hAdd _
      _ = (8 * (s + d) + 4) * 2 := by rw [Nat.mul_succ, Nat.mul_one]
      _ ≤ (8 * (s + d) + 4) * p := Nat.mul_le_mul_left _ hp
      _ < p ^ (s + d) * p := Nat.mul_lt_mul_of_pos_right ih
        (Nat.lt_of_lt_of_le (by decide : 0 < 2) hp)

private theorem affineCutoff_ge_two {p r : Nat} (hp : 2 ≤ p) (hr : 6 ≤ r) :
    8 * r + 4 < p ^ r :=
  affineBound_lt_pow hp (by decide : 1 ≤ 6) hr
    (Nat.lt_of_lt_of_le (by decide : 8 * 6 + 4 < 2 ^ 6) (Nat.pow_le_pow_left hp 6))

private theorem affineCutoff_ge_three {p r : Nat} (hp : 3 ≤ p) (hr : 4 ≤ r) :
    8 * r + 4 < p ^ r :=
  affineBound_lt_pow (Nat.le_trans (by decide : 2 ≤ 3) hp) (by decide : 1 ≤ 4) hr
    (Nat.lt_of_lt_of_le (by decide : 8 * 4 + 4 < 3 ^ 4) (Nat.pow_le_pow_left hp 4))

private theorem affineCutoff_ge_five {p r : Nat} (hp : 5 ≤ p) (hr : 2 ≤ r) :
    8 * r + 4 < p ^ r :=
  affineBound_lt_pow (Nat.le_trans (by decide : 2 ≤ 5) hp) (by decide : 1 ≤ 2) hr
    (Nat.lt_of_lt_of_le (by decide : 8 * 2 + 4 < 5 ^ 2) (Nat.pow_le_pow_left hp 2))

/-- A list containing every characteristic and field-extension degree
meeting the bound. Extra composite bases at exponent one are harmless. -/
def affineLinePrimePowerCandidates : List (Nat × Nat) :=
  [(2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (3, 1), (3, 2), (3, 3),
    (5, 1), (6, 1), (7, 1), (8, 1), (9, 1), (10, 1), (11, 1), (12, 1)]

theorem affineLine_prime_power_candidates {p r : Nat} (hp₂ : 2 ≤ p) (hp₄ : p ≠ 4)
    (hr : 0 < r) (hBound : p ^ r ≤ 8 * r + 4) :
    (p, r) ∈ affineLinePrimePowerCandidates := by
  by_cases h₂ : p = 2
  · subst p
    have hr₆ : r < 6 := Nat.lt_of_not_ge
      (fun h => (Nat.not_lt_of_ge hBound) (affineCutoff_ge_two hp₂ h))
    have rows : ∀ r : Fin 6, 0 < r.val →
        (2, r.val) ∈ affineLinePrimePowerCandidates := by decide
    exact rows ⟨r, hr₆⟩ hr
  by_cases h₃ : p = 3
  · subst p
    have hr₄ : r < 4 := Nat.lt_of_not_ge
      (fun h => (Nat.not_lt_of_ge hBound) (affineCutoff_ge_three (by decide) h))
    have rows : ∀ r : Fin 4, 0 < r.val →
        (3, r.val) ∈ affineLinePrimePowerCandidates := by decide
    exact rows ⟨r, hr₄⟩ hr
  have hp₃ : 3 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hp₂ (fun hEq => h₂ hEq.symm))
  have hp₄' : 4 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hp₃ (fun hEq => h₃ hEq.symm))
  have hp₅ : 5 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hp₄' (fun hEq => hp₄ hEq.symm))
  have hr₁ : r = 1 := by
    by_cases h : r = 1
    · exact h
    · exact False.elim ((Nat.not_lt_of_ge hBound) (affineCutoff_ge_five hp₅
        (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hr (fun hEq => h hEq.symm)))))
  subst r
  simp only [Nat.pow_one] at hBound
  have hTable : ∀ p : Fin 13, 5 ≤ p.val →
      (p.val, 1) ∈ affineLinePrimePowerCandidates := by decide
  exact hTable ⟨p, Nat.lt_succ_of_le hBound⟩ hp₅

/-- In the Paley parameter range, the two-anchor size bound leaves orders
five and nine. -/
theorem affineLine_paley_small_orders {p r : Nat} (hp₂ : 2 ≤ p) (hp₄ : p ≠ 4) (hr : 0 < r)
    (hBound : p ^ r ≤ 8 * r + 4) (hPaley : p ^ r % 4 = 1) :
    p ^ r = 5 ∨ p ^ r = 9 := by
  have h : ∀ a ∈ affineLinePrimePowerCandidates, a.1 ^ a.2 % 4 = 1 →
      a.1 ^ a.2 = 5 ∨ a.1 ^ a.2 = 9 := by
    decide
  exact h (p, r) (affineLine_prime_power_candidates hp₂ hp₄ hr hBound) hPaley

/-- In the Peisert parameter range, the two-anchor bound leaves order nine. -/
theorem affineLine_peisert_small_orders {p r : Nat} (hp₂ : 2 ≤ p) (hp₄ : p ≠ 4) (hr : 0 < r)
    (hBound : p ^ r ≤ 8 * r + 4) (hPrime : p % 4 = 3) (hEven : r % 2 = 0) :
    p ^ r = 9 := by
  have h : ∀ a ∈ affineLinePrimePowerCandidates, a.1 % 4 = 3 → a.2 % 2 = 0 →
      a.1 ^ a.2 = 9 := by
    decide
  exact h (p, r) (affineLine_prime_power_candidates hp₂ hp₄ hr hBound) hPrime hEven

/-- The Van Lint–Schrijver primitive-residue condition forces its even
extension degree. Only three field-order and connection-index pairs
meet the affine-line size bound. -/
theorem affineLine_vanLintSchrijver_small_orders {p r ℓ : Nat}
    (hp₂ : 2 ≤ p) (hp₄ : p ≠ 4) (hr : 0 < r) (hBound : p ^ r ≤ 8 * r + 4)
    (hOdd : ℓ % 2 = 1) (hLarge : 2 < ℓ)
    (hIndex : ℓ ∣ p ^ r - 1) (hOrder : ℓ - 1 ∣ r) :
    (p ^ r = 4 ∧ ℓ = 3) ∨
      (p ^ r = 16 ∧ (ℓ = 3 ∨ ℓ = 5)) := by
  have hp_pos : 0 < p := Nat.lt_of_lt_of_le (by decide : 0 < 2) hp₂
  have hPow : p ≤ p ^ r := by
    simpa only [Nat.pow_one] using (Nat.pow_le_pow_right hp_pos (show 1 ≤ r from hr))
  have hSmall : 0 < p ^ r - 1 :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le hp₂ hPow)
  have hTable : ∀ a ∈ affineLinePrimePowerCandidates, ∀ ℓ : Fin 32,
      ℓ.val % 2 = 1 → 2 < ℓ.val → ℓ.val ∣ a.1 ^ a.2 - 1 → ℓ.val - 1 ∣ a.2 →
      (a.1 ^ a.2 = 4 ∧ ℓ.val = 3) ∨
        (a.1 ^ a.2 = 16 ∧ (ℓ.val = 3 ∨ ℓ.val = 5)) := by
    decide
  have hPower : ∀ a ∈ affineLinePrimePowerCandidates, a.1 ^ a.2 ≤ 32 := by decide
  have hMem := affineLine_prime_power_candidates hp₂ hp₄ hr hBound
  have hℓ := Nat.le_of_dvd hSmall hIndex
  have hUpper := hPower (p, r) hMem
  change p ^ r ≤ 32 at hUpper
  have hℓUpper : ℓ < 32 := Nat.lt_of_lt_of_le
    (Nat.lt_of_le_of_lt hℓ (Nat.sub_lt (Nat.lt_of_lt_of_le hp_pos hPow) (by decide))) hUpper
  exact hTable (p, r) hMem ⟨ℓ, hℓUpper⟩ hOdd hLarge hIndex hOrder

end EPPAIII.Primitive
