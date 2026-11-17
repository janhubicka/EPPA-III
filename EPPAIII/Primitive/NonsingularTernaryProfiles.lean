import EPPAIII.Primitive.AffineSurvivorExclusions

/-!
# A uniform constituent exclusion at the ternary orthogonal profile
-/

namespace EPPAIII.Primitive

open SimpleGraph

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

private theorem half_order_dvd_order {n : ℕ} (hEven : n % 2 = 0) :
    n / 2 ∣ n := ⟨2, by omega⟩

private theorem twice_dvd_order {n t : ℕ} (hEven : n % 2 = 0) (h : t ∣ n / 2) :
    2 * t ∣ n := by
  simpa only [show 2 * (n / 2) = n by omega] using Nat.mul_dvd_mul_left 2 h

private theorem sparse_cover_degree_implies_dvd {n d : ℕ} (hd : d + 1 < n / 2)
    (h : CoverDegreeCompatible n d) : d ∣ n ∨ d + 1 ∣ n ∨ d + 2 ∣ n := by
  obtain ⟨hEven, t, ht, hDiv, hDeg⟩ := h
  have hHalf := half_order_dvd_order hEven
  simp only [coverDegreesAtHalfOrder, Finset.mem_insert, Finset.mem_singleton] at hDeg
  have hTwice := twice_dvd_order hEven hDiv
  rcases hDeg with h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inl (by simpa only [show d + 1 = t.val by omega] using hDiv.trans hHalf))
  · exact Or.inr (Or.inl (by simpa only [show d + 1 = 2 * t.val by omega] using hTwice))
  · exact Or.inl (by simpa only [h] using hDiv.trans hHalf)
  · exact Or.inr (Or.inr (by simpa only [show d + 2 = 2 * t.val by omega] using hTwice))
  all_goals omega

private theorem dense_compl_cover_degree_implies_dvd {n d : ℕ} (hd0 : 2 ≤ d)
    (hd : d + 1 < n / 2) (h : CoverDegreeCompatible n (n - 1 - d)) :
    n % 2 = 0 ∧ ((n / 2 - d) ∣ n / 2 ∨ (n / 2 - d + 1) ∣ n / 2) := by
  obtain ⟨hEven, t, ht, hDiv, hDeg⟩ := h
  have htLe : t.val ≤ n / 2 := Nat.le_of_lt_succ t.isLt
  have htCases : t.val = n / 2 ∨ 2 * t.val ≤ n / 2 := by
    obtain ⟨k, hk⟩ := hDiv
    by_cases hk2 : 2 ≤ k
    · right
      calc
        2 * t.val ≤ t.val * k := by simpa only [Nat.mul_comm 2] using Nat.mul_le_mul_left t.val hk2
        _ = n / 2 := hk.symm
    · have hk1 : k = 1 := by
        by_contra hk1
        have hz : k = 0 := by omega
        rw [hz, Nat.mul_zero] at hk
        omega
      exact Or.inl (by simpa only [hk1, Nat.mul_one] using hk.symm)
  refine ⟨hEven, ?_⟩
  simp only [coverDegreesAtHalfOrder, Finset.mem_insert, Finset.mem_singleton] at hDeg
  rcases hDeg with h | h | h | h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact Or.inl (by simpa only [show n / 2 - d = t.val by omega] using hDiv)
  · omega
  · exact Or.inr (by simpa only [show n / 2 - d + 1 = t.val by omega] using hDiv)

/-- The published parameters of `NO^ε_(2m)(3)`, using the integer
`a = (3^(m-2) - 1)/2`. The Boolean selects the positive sign. -/
def evenTernaryParameters (a : ℕ) (plus : Bool) : SRGParameters :=
  let r := 2 * a + 1
  let k := 3 * r * (3 * a + if plus then 1 else 2)
  let l := r * (3 * a + if plus then 2 else 1)
  let d := 3 * r * r
  ⟨k + 3 * d, k, l, k - d⟩

private theorem ternary_local_numeric_screen (a : ℕ) (ha : 3 ≤ a) (plus : Bool) :
    let p := evenTernaryParameters a plus
    let n := p.degree
    let d := p.adjacentCommon
    0 < n ∧ d < n ∧ ¬ (d + 1) ∣ n ∧ ¬ (n - d) ∣ n ∧
      ¬ CoverDegreeCompatible n d ∧ ¬ CoverDegreeCompatible n (n - 1 - d) := by
  let p := evenTernaryParameters a plus
  let n := p.degree
  let d := p.adjacentCommon
  change 0 < n ∧ d < n ∧ ¬ (d + 1) ∣ n ∧ ¬ (n - d) ∣ n ∧
    ¬ CoverDegreeCompatible n d ∧ ¬ CoverDegreeCompatible n (n - 1 - d)
  have hD : 2 ≤ d := by cases plus <;> simp [d, p, evenTernaryParameters] <;> nlinarith
  have hDensity : 2 * (d + 2) < n := by
    cases plus <;> simp [n, d, p, evenTernaryParameters] <;> nlinarith
  have hRatio (j : ℕ) (hj : j ≤ 2) : ¬ (d + j) ∣ n := by
    cases plus
    · apply not_dvd_of_between_multiples (k := 3) <;>
        simp [n, d, p, evenTernaryParameters] <;> nlinarith
    · apply not_dvd_of_between_multiples (k := 2)
      · omega
      · simp [n, d, p, evenTernaryParameters]
        nlinarith
  have hComplRatio (hEven : n % 2 = 0) (j : ℕ) (hj : j ≤ 1) :
      ¬ (n / 2 - d + j) ∣ n / 2 := by
    let m := n / 2
    have hm : 2 * m = n := by omega
    have hmt : d ≤ m := by omega
    cases plus
    · apply not_dvd_of_between_multiples (k := 2)
      · have hI : n + 4 * j < 4 * d := by
          simp [n, d, p, evenTernaryParameters]
          nlinarith
        omega
      · have hI : 3 * d < n := by
          simp [n, d, p, evenTernaryParameters]
          nlinarith
        omega
    · apply not_dvd_of_between_multiples (k := 3)
      · have hI : n + 3 * j < 3 * d := by
          simp [n, d, p, evenTernaryParameters]
          nlinarith
        omega
      · have hI : 8 * d < 3 * n := by
          simp [n, d, p, evenTernaryParameters]
          nlinarith [mul_nonneg (show 0 ≤ a - 3 by omega) (show 0 ≤ 2 * a + 1 by omega)]
        omega
  refine ⟨by omega, by omega, hRatio 1 (by decide), ?_, ?_, ?_⟩
  · apply not_dvd_of_between_multiples (k := 1) <;> omega
  · intro h
    rcases sparse_cover_degree_implies_dvd (by omega) h with h | h | h
    · exact hRatio 0 (by decide) (by simpa only [Nat.add_zero] using h)
    · exact hRatio 1 (by decide) h
    · exact hRatio 2 (by decide) h
  · intro h
    obtain ⟨hEven, h | h⟩ := dense_compl_cover_degree_implies_dvd hD (by omega) h
    · exact hComplRatio hEven 0 (by decide) (by simpa only [Nat.add_zero] using h)
    · exact hComplRatio hEven 1 (by decide) h

/-- The local constituent of an even ternary orthogonal graph is excluded
using only the host SRG parameters. The plus branch at `a=1` has the only
complemented cover candidate left by the numerical screen; its common
neighbours exceed the ambient codegree. -/
theorem evenTernary_local_excludes_forms {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {a : ℕ} (ha : 1 ≤ a) (plus : Bool)
    (hHost : let p := evenTernaryParameters a plus
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (root : V) :
    let G := constituentGraph H root false
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  have h := constituentGraph_profile H (evenTernaryParameters a plus) hHost root false
  by_cases ha3 : 3 ≤ a
  · obtain ⟨hn, hd, hUnion, hUnionCompl, hCover, hCoverCompl⟩ :=
      ternary_local_numeric_screen a ha3 plus
    exact regular_profile_excludes_all_forms h hn hd hUnion hUnionCompl hCover hCoverCompl
  have ha12 : a = 1 ∨ a = 2 := by omega
  rcases ha12 with rfl | rfl <;> cases plus
  · exact regular_profile_excludes_all_forms (n := 45) (d := 12)
      h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · let inclusion : constituentGraph H root false ↪g H :=
      ⟨Function.Embedding.subtype _, Iff.rfl⟩
    exact exclude_forms_of_complement_codegree inclusion (n := 36) (d := 15)
      (m := 18) (t₀ := 3) (μ := 9) h (by decide) (by decide) rfl
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ hxy hnxy => hHost.of_not_adj hxy hnxy) (Or.inl (by decide))
  · exact regular_profile_excludes_all_forms (n := 120) (d := 35)
      h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact regular_profile_excludes_all_forms (n := 105) (d := 40)
      h (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end EPPAIII.Primitive
