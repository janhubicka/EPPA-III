import EPPAIII.Primitive.G2ConstituentExclusions

/-!
# A uniform constituent exclusion at the ternary orthogonal profile
-/

namespace EPPAIII.Primitive

private theorem not_dvd_of_between_multiples {a n k : ℕ}
    (hl : a * k < n) (hu : n < a * (k + 1)) : ¬ a ∣ n := by
  rintro ⟨j, rfl⟩
  by_cases hj : j ≤ k
  · exact (not_lt_of_ge (Nat.mul_le_mul_left a hj)) hl
  · have hk : k + 1 ≤ j := by omega
    exact (not_lt_of_ge (Nat.mul_le_mul_left a hk)) hu

private theorem tripled_odd_degree_no_cover (a : ℕ) (ha : 3 ≤ a) :
    ¬ CoverDegreeCompatible (6 * a + 2) (2 * a + 1) := by
  rintro ⟨_, t, ht, hDiv, hDeg⟩
  have hHalf : (6 * a + 2) / 2 = 3 * a + 1 := by omega
  generalize t.val = u at hDiv hDeg ht
  rw [hHalf] at hDiv hDeg
  simp only [coverDegreesAtHalfOrder, Finset.mem_insert, Finset.mem_singleton] at hDeg
  rcases hDeg with h | h | h | h | h | h | h | h
  · have := not_dvd_of_between_multiples (a := u) (n := 3 * a + 1) (k := 1)
      (by omega) (by omega)
    exact this hDiv
  · have := not_dvd_of_between_multiples (a := u) (n := 3 * a + 1) (k := 2)
      (by omega) (by omega)
    exact this hDiv
  · have := not_dvd_of_between_multiples (a := u) (n := 3 * a + 1) (k := 1)
      (by omega) (by omega)
    exact this hDiv
  all_goals omega

private theorem tripled_odd_degree_no_compl_cover (a : ℕ) (ha : 3 ≤ a) :
    ¬ CoverDegreeCompatible (6 * a + 2) (4 * a) := by
  rintro ⟨_, t, ht, hDiv, hDeg⟩
  have hHalf : (6 * a + 2) / 2 = 3 * a + 1 := by omega
  generalize t.val = u at hDiv hDeg ht
  rw [hHalf] at hDiv hDeg
  have hBound : u ≤ 3 * a + 1 := Nat.le_of_dvd (by omega) hDiv
  simp only [coverDegreesAtHalfOrder, Finset.mem_insert, Finset.mem_singleton] at hDeg
  rcases hDeg with h | h | h | h | h | h | h | h
  · omega
  · omega
  · omega
  · have := not_dvd_of_between_multiples (a := u) (n := 3 * a + 1) (k := 1)
      (by omega) (by omega)
    exact this hDiv
  · omega
  · have := not_dvd_of_between_multiples (a := u) (n := 3 * a + 1) (k := 3)
      (by omega) (by omega)
    exact this hDiv
  · omega
  · have := not_dvd_of_between_multiples (a := u) (n := 3 * a + 1) (k := 2)
      (by omega) (by omega)
    exact this hDiv

/-- A graph with regular profile `(3 * d - 1, d)` for odd `d ≥ 7`
has neither a clique-union nor a generalized-cover model, in either orientation.
In particular this applies to the second constituent of the ternary
nonsingular even-dimensional orthogonal graphs. -/
theorem tripled_odd_degree_excludes_forms {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (hd : 7 ≤ d) (hOdd : d % 2 = 1)
    (h : HasRegularProfile G (3 * d - 1, d)) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  let a := d / 2
  have ha : 3 ≤ a := by omega
  have hD : d = 2 * a + 1 := by omega
  have hN : 3 * d - 1 = 6 * a + 2 := by omega
  rw [hN, hD] at h
  apply regular_profile_excludes_all_forms h (by omega) (by omega)
  · apply not_dvd_of_between_multiples (k := 2) <;> omega
  · apply not_dvd_of_between_multiples (k := 1) <;> omega
  · exact tripled_odd_degree_no_cover a ha
  · rw [show 6 * a + 2 - 1 - (2 * a + 1) = 4 * a by omega]
    exact tripled_odd_degree_no_compl_cover a ha

end EPPAIII.Primitive
