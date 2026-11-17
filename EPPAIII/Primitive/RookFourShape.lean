import EPPAIII.Primitive.RookDensity
import Mathlib.Tactic.Push

/-!
# Classifying dense four-by-four selections by their two-edge matchings

At order eight or more, the absence of same-direction induced matchings
forces a three-by-three corner with one opposite diagonal point. The
absence of opposite-direction matchings forces two parallel lines.
-/

namespace EPPAIII.Primitive.RookDensity

open Finset
open scoped BigOperators

private abbrev R4Cell := Fin 4 × Fin 4

/-- Two opposite stars whose union induces two edges. -/
def HasOppositeStars (S : Finset R4Cell) : Prop :=
  ∃ r c : Fin 4, 2 ≤ ((row S r).erase c).card ∧
    2 ≤ ((row (transpose S) c).erase r).card

private theorem transpose_transpose (S : Finset R4Cell) : transpose (transpose S) = S := by
  ext ⟨r, c⟩
  simp

private theorem oppositeStars_transpose (S : Finset R4Cell) :
    HasOppositeStars (transpose S) ↔ HasOppositeStars S := by
  rw [HasOppositeStars, transpose_transpose, HasOppositeStars]
  exact ⟨fun ⟨r, c, ha, hb⟩ => ⟨c, r, hb, ha⟩, fun ⟨r, c, ha, hb⟩ => ⟨c, r, hb, ha⟩⟩

private theorem card_erase_ge_two {s : Finset (Fin 4)} {a : Fin 4}
    (h : 3 ≤ s.card) : 2 ≤ (s.erase a).card := by
  by_cases ha : a ∈ s
  · have hAdd := card_erase_add_one ha
    omega
  · rw [erase_eq_of_notMem ha]
    omega

private theorem finFour_full {s : Finset (Fin 4)} (h : s.card = 4) (x : Fin 4) : x ∈ s := by
  have he : s = univ := eq_of_subset_of_card_le (subset_univ _) (by simpa using h.ge)
  simp [he]

private theorem dense_rows_have_two (S : Finset R4Cell) (hSize : 8 ≤ S.card)
    (hMax : ∀ r, (row S r).card ≤ 2) (r : Fin 4) :
    (row S r).card = 2 := by
  have hSum := sum_erase_add (univ : Finset (Fin 4)) (fun r => (row S r).card) (mem_univ r)
  rw [← sum_row_card] at hSum
  have hOthers : (∑ a ∈ (univ : Finset (Fin 4)).erase r, (row S a).card) ≤
      ∑ _a ∈ (univ : Finset (Fin 4)).erase r, 2 := sum_le_sum fun a _ => hMax a
  simp at hOthers
  have hR := hMax r
  omega

private theorem two_rows_of_noOppositeStars (S : Finset R4Cell) (hSize : 8 ≤ S.card)
    (hNo : ¬ HasOppositeStars S)
    (r : Fin 4) (hR : 3 ≤ (row S r).card) :
    ∃ s : Fin 4, r ≠ s ∧ ∀ x ∈ S, x.1 = r ∨ x.1 = s := by
  let T := S.filter fun x => x.1 ≠ r
  have hOffCount (c : Fin 4) : ((row (transpose S) c).erase r).card ≤ 1 := by
    by_contra! hBad
    exact hNo ⟨r, c, card_erase_ge_two hR, hBad⟩
  have hColumnInjective : Set.InjOn Prod.snd (T : Set R4Cell) := by
    intro x hx y hy hEq
    obtain ⟨r₁, c₁⟩ := x
    obtain ⟨r₂, c₂⟩ := y
    change c₁ = c₂ at hEq
    subst c₂
    by_contra hBad
    have hr : r₁ ≠ r₂ := fun he => hBad (Prod.ext he rfl)
    obtain ⟨hxS, hxr⟩ := mem_filter.mp hx
    obtain ⟨hyS, hyr⟩ := mem_filter.mp hy
    have hx' : r₁ ∈ (row (transpose S) c₁).erase r :=
      mem_erase.mpr ⟨hxr, (mem_row _ _ _).mpr ((mem_transpose _ _ _).mpr hxS)⟩
    have hy' : r₂ ∈ (row (transpose S) c₁).erase r :=
      mem_erase.mpr ⟨hyr, (mem_row _ _ _).mpr ((mem_transpose _ _ _).mpr hyS)⟩
    have h := one_lt_card_iff.mpr ⟨r₁, r₂, hx', hy', hr⟩
    exact (not_lt_of_ge (hOffCount c₁)) h
  have hImage := card_image_iff.mpr hColumnInjective
  have hTMax : T.card ≤ 4 := by
    rw [← hImage]
    simpa using card_le_card (subset_univ (T.image Prod.snd))
  have hSplit : (row S r).card + T.card = S.card := by
    rw [row_card_filter]
    exact card_filter_add_card_filter_not (fun x : R4Cell => x.1 = r)
  have hRowMax := row_card_le S r
  have hRowFull : (row S r).card = 4 := by omega
  have hTFull : T.card = 4 := by omega
  have hCols (c : Fin 4) : ∃ t : Fin 4, t ≠ r ∧ (t, c) ∈ S := by
    have hc := finFour_full (hImage.trans hTFull) c
    obtain ⟨⟨t, c'⟩, ht, hc'⟩ := mem_image.mp hc
    change c' = c at hc'
    subst c'
    exact ⟨t, (mem_filter.mp ht).2, (mem_filter.mp ht).1⟩
  have hSome : ∃ s, s ≠ r ∧ 2 ≤ (row S s).card := by
    by_contra! hNone
    have hOtherSum := sum_erase_add (univ : Finset (Fin 4)) (fun s => (row S s).card)
      (mem_univ r)
    rw [← sum_row_card] at hOtherSum
    have hOtherLe : (∑ s ∈ (univ : Finset (Fin 4)).erase r, (row S s).card) ≤
        ∑ _s ∈ (univ : Finset (Fin 4)).erase r, 1 := by
      apply sum_le_sum
      intro s hs
      exact Nat.le_of_lt_succ (hNone s (mem_erase.mp hs).1)
    simp at hOtherLe
    omega
  obtain ⟨s, hsr, hs⟩ := hSome
  have hsFull (c : Fin 4) : (s, c) ∈ S := by
    by_contra hc
    have hc' : c ∉ row S s := fun hm => hc ((mem_row S s c).mp hm)
    obtain ⟨t, htr, ht⟩ := hCols c
    have hts : t ≠ s := fun e => hc (e ▸ ht)
    have hrc : (r, c) ∈ S := (mem_row S r c).mp (finFour_full hRowFull c)
    have hCol : 1 < ((row (transpose S) c).erase s).card :=
      one_lt_card_iff.mpr ⟨r, t,
        mem_erase.mpr ⟨hsr.symm, (mem_row _ _ _).mpr ((mem_transpose _ _ _).mpr hrc)⟩,
        mem_erase.mpr ⟨hts, (mem_row _ _ _).mpr ((mem_transpose _ _ _).mpr ht)⟩, htr.symm⟩
    exact hNo ⟨s, c, by simpa only [erase_eq_of_notMem hc'] using hs, hCol⟩
  refine ⟨s, hsr.symm, ?_⟩
  rintro ⟨a, c⟩ hx
  by_cases har : a = r
  · exact Or.inl har
  · exact Or.inr (congrArg Prod.fst (hColumnInjective
      (mem_filter.mpr ⟨hx, har⟩) (mem_filter.mpr ⟨hsFull c, hsr⟩) rfl))

/-- At least eight cells with no opposite induced matching lie in two parallel lines. -/
theorem rookFourStripe_of_noOppositeStars (S : Finset R4Cell) (hSize : 8 ≤ S.card)
    (hNo : ¬ HasOppositeStars S) :
    (∃ r s : Fin 4, r ≠ s ∧ ∀ x ∈ S, x.1 = r ∨ x.1 = s) ∨
      (∃ r s : Fin 4, r ≠ s ∧ ∀ x ∈ S, x.2 = r ∨ x.2 = s) := by
  by_cases hRows : ∃ r, 3 ≤ (row S r).card
  · obtain ⟨r, hr⟩ := hRows
    obtain ⟨s, hrs, hS⟩ := two_rows_of_noOppositeStars S hSize hNo r hr
    exact Or.inl ⟨r, s, hrs, hS⟩
  by_cases hCols : ∃ c, 3 ≤ (row (transpose S) c).card
  · obtain ⟨r, hr⟩ := hCols
    obtain ⟨s, hrs, hS⟩ := two_rows_of_noOppositeStars (transpose S)
      (by simpa using hSize) (fun h => hNo ((oppositeStars_transpose S).mp h)) r hr
    exact Or.inr ⟨r, s, hrs, fun x hx => hS (x.2, x.1) ((mem_transpose _ _ _).mpr hx)⟩
  push Not at hRows hCols
  have hr := dense_rows_have_two S hSize (fun i => Nat.le_of_lt_succ (hRows i)) 0
  have hc (c : Fin 4) := dense_rows_have_two (transpose S)
    (by simpa using hSize) (fun i => Nat.le_of_lt_succ (hCols i)) c
  have hlt : (row S 0).card < (univ : Finset (Fin 4)).card := by simp [hr]
  obtain ⟨c, _, hcr⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hrc : (0 : Fin 4) ∉ row (transpose S) c := by
    simpa only [mem_row, mem_transpose] using hcr
  exact (hNo ⟨0, c, by simp [hcr, hr], by simp [hrc, hc]⟩).elim


private theorem corner_or_missing_column_of_row_card_three (S : Finset R4Cell) (hSize : 8 ≤ S.card)
    (hNoRow : ¬ SameOrientation S) (hNoCol : ¬ SameOrientation (transpose S))
    (r : Fin 4) (hr : (row S r).card = 3) :
    (∃ a c : Fin 4, ∀ x ∈ S, x.1 = a ↔ x.2 = c) ∨ (∃ c : Fin 4, ∀ x ∈ S, x.2 ≠ c) := by
  let C := row S r
  have hlt : C.card < (univ : Finset (Fin 4)).card := by simp [C, hr]
  obtain ⟨c, _, hc⟩ := exists_mem_notMem_of_card_lt_card hlt
  have hComplete : C = univ.erase c := by
    apply eq_of_subset_of_card_le
    · intro a ha
      exact mem_erase.mpr ⟨fun e => hc (e ▸ ha), mem_univ _⟩
    · simp [C, hr]
  let A := row (transpose S) c
  let B := univ \ A
  have hAOne (s : Fin 4) (hs : s ∈ A) : (row S s).card ≤ 1 := by
    by_contra! hh
    have hsc : c ∈ row S s := (mem_row _ _ _).mpr
      ((mem_transpose _ _ _).mp ((mem_row _ _ _).mp hs))
    exact hNoRow (disjointPairs_of_outside S hr.ge hh hsc hc)
  have hMax (s : Fin 4) : (row S s).card ≤ 3 :=
    row_card_le_three_of_no_sameOrientation S hSize hNoRow s
  have hSplit : A.card + B.card = 4 := by
    simpa [A, B, add_comm] using card_sdiff_add_card_eq_card (subset_univ A)
  have hParts : (∑ s ∈ B, (row S s).card) + ∑ s ∈ A, (row S s).card = S.card := by
    have hh := sum_sdiff (s₁ := A) (s₂ := univ) (subset_univ A) (f := fun s => (row S s).card)
    simpa [B, ← sum_row_card S] using hh
  have hAUpper : (∑ s ∈ A, (row S s).card) ≤ A.card := by
    simpa using sum_le_sum (f := fun s => (row S s).card) (g := fun _ => 1) hAOne
  have hBUpper : (∑ s ∈ B, (row S s).card) ≤ 3 * B.card := by
    simpa [Nat.mul_comm] using sum_le_sum (f := fun s => (row S s).card)
      (g := fun _ => 3) (fun s _ => hMax s : ∀ s ∈ B, _)
  have hAMax : A.card ≤ 2 := by omega
  have hANotTwo : A.card ≠ 2 := by
    intro hTwo
    have hBTwo : B.card = 2 := by omega
    have hRNotA : r ∉ A := by
      simpa only [A, mem_row, mem_transpose] using (show (r, c) ∉ S from
        fun hr' => hc ((mem_row S r c).mpr hr'))
    have hrB : r ∈ B := mem_sdiff.mpr ⟨mem_univ _, hRNotA⟩
    have hBFull (s : Fin 4) (hs : s ∈ B) : (row S s).card = 3 := by
      have hRemove := sum_erase_add B (fun s => (row S s).card) hs
      have hOther : (∑ a ∈ B.erase s, (row S a).card) ≤ 3 := by
        have hh : (∑ a ∈ B.erase s, (row S a).card) ≤ ∑ _a ∈ B.erase s, 3 :=
          sum_le_sum fun a _ => hMax a
        simpa [card_erase_of_mem hs, hBTwo] using hh
      have h := hMax s
      omega
    have hBC (s : Fin 4) (hs : s ∈ B) : row S s = C := by
      apply eq_of_subset_of_card_le
      · have hsA := (mem_sdiff.mp hs).2
        intro a ha
        rw [hComplete]
        refine mem_erase.mpr ⟨fun e => hsA ?_, mem_univ _⟩
        subst a
        exact (mem_row _ _ _).mpr ((mem_transpose _ _ _).mpr ((mem_row _ _ _).mp ha))
      · exact (hBFull s hs).trans hr.symm |>.ge
    obtain ⟨d, hd⟩ : C.Nonempty := card_pos.mp (by simp [C, hr])
    have hdc : d ≠ c := fun h => hc (h ▸ hd)
    apply hNoCol
    refine ⟨c, d, hdc.symm, A, B, Subset.rfl, ?_, hTwo, hBTwo, ?_⟩
    · intro s hs
      exact (mem_row _ _ _).mpr ((mem_transpose _ _ _).mpr
        ((mem_row _ _ _).mp ((hBC s hs).symm ▸ hd)))
    · exact disjoint_left.mpr fun s hsA hsB => (mem_sdiff.mp hsB).2 hsA
  have hAAtMostOne : A.card ≤ 1 := by omega
  by_cases hEmpty : A = ∅
  · right
    refine ⟨c, ?_⟩
    rintro ⟨i, j⟩ hij h
    change j = c at h
    subst j
    have hi : i ∈ A := (mem_row _ _ _).mpr ((mem_transpose _ _ _).mpr hij)
    simp [hEmpty] at hi
  · left
    have hAPos : 0 < A.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hEmpty)
    obtain ⟨a, ha⟩ := card_eq_one.mp (show A.card = 1 by omega)
    refine ⟨a, c, ?_⟩
    rintro ⟨i, j⟩ hij
    change i = a ↔ j = c
    have hac : (a, c) ∈ S := by
      have hMem : a ∈ A := by simp [ha]
      exact (mem_transpose _ _ _).mp ((mem_row _ _ _).mp hMem)
    constructor
    · intro h
      subst i
      by_contra hj
      have hMem : a ∈ A := by simp [ha]
      have hOne := hAOne a hMem
      have hh : 1 < (row S a).card := one_lt_card_iff.mpr
        ⟨j, c, (mem_row _ _ _).mpr hij, (mem_row _ _ _).mpr hac, hj⟩
      omega
    · intro h
      subst j
      have hi : i ∈ A := (mem_row _ _ _).mpr ((mem_transpose _ _ _).mpr hij)
      simpa [ha] using hi

private theorem noSame_of_allTwo_false (S : Finset R4Cell) (hNo : ¬ SameOrientation S)
    (hRows : ∀ r, (row S r).card = 2) (hCols : ∀ c, (row (transpose S) c).card = 2) :
    False := by
  obtain ⟨a, b, hab, hAB⟩ := card_eq_two.mp (hRows 0)
  have hMeet (r : Fin 4) (hr : r ≠ 0) : ∃ c, c ∈ row S r ∧ c ∈ row S 0 := by
    by_contra hNone
    exact hNo ⟨r, 0, hr, row S r, row S 0, Subset.rfl, Subset.rfl, hRows r, hRows 0,
      disjoint_left.mpr fun c h₁ h₂ => hNone ⟨c, h₁, h₂⟩⟩
  obtain ⟨c₁, c₁r, c₁o⟩ := hMeet 1 (by decide)
  obtain ⟨c₂, c₂r, c₂o⟩ := hMeet 2 (by decide)
  obtain ⟨c₃, c₃r, c₃o⟩ := hMeet 3 (by decide)
  have hDistinct {c : Fin 4} {i j : Fin 4} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
      (hc : c ∈ row S 0) (hci : c ∈ row S i) (hcj : c ∈ row S j) : False := by
    have hSubset : ({0, i, j} : Finset (Fin 4)) ⊆ row (transpose S) c := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rw [mem_row, mem_transpose]
      rcases hx with rfl | rfl | rfl
      · exact (mem_row _ _ _).mp hc
      · exact (mem_row _ _ _).mp hci
      · exact (mem_row _ _ _).mp hcj
    have hLarge := card_le_card hSubset
    simp [hCols c, hi.symm, hj.symm, hij] at hLarge
  have hCoincide : c₁ = c₂ ∨ c₁ = c₃ ∨ c₂ = c₃ := by
    rw [hAB] at c₁o c₂o c₃o
    simp only [mem_insert, mem_singleton] at c₁o c₂o c₃o
    grind
  rcases hCoincide with h | h | h
  · exact hDistinct (by decide : (1 : Fin 4) ≠ 0) (by decide : (2 : Fin 4) ≠ 0)
      (by decide) c₁o c₁r (h.symm ▸ c₂r)
  · exact hDistinct (by decide : (1 : Fin 4) ≠ 0) (by decide : (3 : Fin 4) ≠ 0)
      (by decide) c₁o c₁r (h.symm ▸ c₃r)
  · exact hDistinct (by decide : (2 : Fin 4) ≠ 0) (by decide : (3 : Fin 4) ≠ 0)
      (by decide) c₂o c₂r (h.symm ▸ c₃r)

private theorem corner_of_row_card_three (S : Finset R4Cell) (hSize : 8 ≤ S.card)
    (hNoRow : ¬ SameOrientation S) (hNoCol : ¬ SameOrientation (transpose S))
    (r : Fin 4) (hR : (row S r).card = 3) :
    ∃ a c : Fin 4, ∀ x ∈ S, x.1 = a ↔ x.2 = c := by
  rcases corner_or_missing_column_of_row_card_three S hSize hNoRow hNoCol r hR with hCorner | ⟨c, hMissing⟩
  · exact hCorner
  have hTransposeSize : 8 ≤ (transpose S).card := by simpa using hSize
  have hNoSecond : ¬ SameOrientation (transpose (transpose S)) := by
    rw [transpose_transpose]
    exact hNoRow
  have hColTall : ∃ d, (row (transpose S) d).card = 3 := by
    by_contra hNone
    have hColLe (d : Fin 4) : (row (transpose S) d).card ≤ 2 := by
      have hMax := row_card_le_three_of_no_sameOrientation (transpose S) hTransposeSize hNoCol d
      have hNe : (row (transpose S) d).card ≠ 3 := fun h => hNone ⟨d, h⟩
      omega
    have hTwo := dense_rows_have_two (transpose S) hTransposeSize hColLe c
    have hEmpty : row (transpose S) c = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hMissing (a, c) ((mem_transpose _ _ _).mp ((mem_row _ _ _).mp ha)) rfl
    simp [hEmpty] at hTwo
  obtain ⟨d, hd⟩ := hColTall
  rcases corner_or_missing_column_of_row_card_three (transpose S) hTransposeSize hNoCol hNoSecond d hd with
    ⟨e, a, hh⟩ | ⟨a, hh⟩
  · exact ⟨a, e, fun x hx => (hh (x.2, x.1) ((mem_transpose _ _ _).mpr hx)).symm⟩
  · exact ⟨a, c, fun x hx =>
      iff_of_false (hh (x.2, x.1) ((mem_transpose _ _ _).mpr hx)) (hMissing x hx)⟩

/-- At least eight cells with no same-direction matching lie in a three-by-three
corner with its one opposite diagonal point. -/
theorem rookFourCorner_of_noSameStars (S : Finset R4Cell) (hSize : 8 ≤ S.card)
    (hNoRow : ¬ SameOrientation S) (hNoCol : ¬ SameOrientation (transpose S)) :
    ∃ a c : Fin 4, ∀ x ∈ S, x.1 = a ↔ x.2 = c := by
  by_cases hRows : ∃ r, (row S r).card = 3
  · obtain ⟨r, hr⟩ := hRows
    exact corner_of_row_card_three S hSize hNoRow hNoCol r hr
  by_cases hCols : ∃ c, (row (transpose S) c).card = 3
  · obtain ⟨c, hc⟩ := hCols
    obtain ⟨p, q, hpq⟩ := corner_of_row_card_three (transpose S) (by simpa using hSize)
      hNoCol (by simpa only [transpose_transpose] using hNoRow) c hc
    exact ⟨q, p, fun x hx => (hpq (x.2, x.1) ((mem_transpose _ _ _).mpr hx)).symm⟩
  have hRowMax (r : Fin 4) : (row S r).card ≤ 2 := by
    have hMax := row_card_le_three_of_no_sameOrientation S hSize hNoRow r
    have hNe : (row S r).card ≠ 3 := fun h => hRows ⟨r, h⟩
    omega
  have hTSize : 8 ≤ (transpose S).card := by simpa using hSize
  have hColMax (c : Fin 4) : (row (transpose S) c).card ≤ 2 := by
    have hMax := row_card_le_three_of_no_sameOrientation (transpose S) hTSize hNoCol c
    have hNe : (row (transpose S) c).card ≠ 3 := fun h => hCols ⟨c, h⟩
    omega
  exact (noSame_of_allTwo_false S hNoRow (dense_rows_have_two S hSize hRowMax)
    (dense_rows_have_two (transpose S) hTSize hColMax)).elim
end EPPAIII.Primitive.RookDensity
