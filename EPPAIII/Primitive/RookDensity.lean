import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Prod

/-!
# Two induced matching-edge configurations in a half-dense square matrix

A star means two selected cells in a single row or column. A dense
selection contains two disjoint stars with the same orientation as well
as two disjoint stars with different orientations.
-/

namespace EPPAIII.Primitive.RookDensity

open Finset
open scoped BigOperators

variable {n : ℕ}

/-- The selected columns of one row. -/
def row (S : Finset (Fin n × Fin n)) (r : Fin n) : Finset (Fin n) :=
  univ.filter fun c => (r, c) ∈ S

@[simp] theorem mem_row (S : Finset (Fin n × Fin n)) (r c : Fin n) :
    c ∈ row S r ↔ (r, c) ∈ S := by
  simp [row]

/-- Transpose a square selection. -/
def transpose (S : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) :=
  S.map (Equiv.prodComm (Fin n) (Fin n)).toEmbedding

@[simp] theorem mem_transpose (S : Finset (Fin n × Fin n)) (r c : Fin n) :
    (r, c) ∈ transpose S ↔ (c, r) ∈ S := by
  simp [transpose]

@[simp] theorem card_transpose (S : Finset (Fin n × Fin n)) : (transpose S).card = S.card := by
  simp [transpose]

private theorem row_card_filter (S : Finset (Fin n × Fin n)) (r : Fin n) :
    (row S r).card = (S.filter fun p => p.1 = r).card := by
  apply Finset.card_bij (fun c _ => (r, c))
  · intro c hc
    exact mem_filter.mpr ⟨(mem_row S r c).mp hc, rfl⟩
  · intro c _ d _ h
    exact congrArg Prod.snd h
  · rintro ⟨r', c⟩ h
    obtain ⟨h, hEq⟩ := mem_filter.mp h
    change r' = r at hEq
    subst r'
    exact ⟨c, (mem_row S r c).mpr h, rfl⟩

private theorem sum_row_card (S : Finset (Fin n × Fin n)) :
    S.card = ∑ r : Fin n, (row S r).card := by
  have h :=
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := univ)
      (fun _ _ => mem_univ _)
  rw [h]
  exact sum_congr rfl fun r _ => (row_card_filter S r).symm

private theorem row_card_le (S : Finset (Fin n × Fin n)) (r : Fin n) :
    (row S r).card ≤ n := by
  simpa using Finset.card_le_card (Finset.subset_univ (row S r))

/-- Two rows containing stars whose column pairs are disjoint. -/
def SameOrientation (S : Finset (Fin n × Fin n)) : Prop :=
  ∃ r r' : Fin n, r ≠ r' ∧ ∃ A B : Finset (Fin n),
    A ⊆ row S r ∧ B ⊆ row S r' ∧ A.card = 2 ∧ B.card = 2 ∧ Disjoint A B

private theorem card_sdiff_ge_two {A B : Finset (Fin n)} (h : B.card + 2 ≤ A.card) :
    2 ≤ (A \ B).card := by
  have hAdd := card_sdiff_add_card_inter A B
  have hLe := card_le_card (inter_subset_right (s₁ := A) (s₂ := B))
  omega

private theorem disjointPairs_of_large (S : Finset (Fin n × Fin n)) {r r' : Fin n}
    (hn : r ≠ r') (hR : 4 ≤ (row S r).card) (hR' : 2 ≤ (row S r').card) :
    SameOrientation S := by
  obtain ⟨B, hB, hPairB⟩ := exists_subset_card_eq hR'
  obtain ⟨A, hA, hPairA⟩ :=
    exists_subset_card_eq (card_sdiff_ge_two (A := row S r) (B := B) (by omega))
  refine ⟨r, r', hn, A, B, fun _ hc => (mem_sdiff.mp (hA hc)).1, hB, hPairA, hPairB, ?_⟩
  exact disjoint_left.mpr fun _ ha hb => (mem_sdiff.mp (hA ha)).2 hb

private theorem disjointPairs_of_outside (S : Finset (Fin n × Fin n)) {r r' : Fin n}
    (hR : 3 ≤ (row S r).card) (hR' : 2 ≤ (row S r').card)
    {c : Fin n} (hc : c ∈ row S r') (hOutside : c ∉ row S r) :
    SameOrientation S := by
  have hne : r ≠ r' := fun h => hOutside (h ▸ hc)
  have hDiff : ({c} : Finset (Fin n)).card < (row S r').card := by simp; omega
  obtain ⟨d, hd, hdne⟩ := exists_mem_notMem_of_card_lt_card hDiff
  rw [mem_singleton] at hdne
  obtain ⟨A, hA, hPairA⟩ :=
    exists_subset_card_eq (card_sdiff_ge_two (A := row S r) (B := {d}) (by simpa using hR))
  refine ⟨r, r', hne, A, {c, d}, (fun _ hx => (mem_sdiff.mp (hA hx)).1),
    ?_, hPairA, by simp [Ne.symm hdne], ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hc
    · exact (mem_singleton.mp hx).symm ▸ hd
  · apply disjoint_left.mpr
    intro x hx hPair
    rcases mem_insert.mp hPair with rfl | hPair
    · exact hOutside (mem_sdiff.mp (hA hx)).1
    · exact (mem_sdiff.mp (hA hx)).2 hPair

private theorem dense_row_three (S : Finset (Fin n × Fin n))
    (hSize : 2 * n < S.card) :
    ∃ r : Fin n, 3 ≤ (row S r).card := by
  by_contra hNone
  have hRows (r : Fin n) : (row S r).card ≤ 2 := by
    by_contra hh
    exact hNone ⟨r, by omega⟩
  have hSum : (∑ r : Fin n, (row S r).card) ≤ ∑ _r : Fin n, 2 :=
    sum_le_sum fun r _ => hRows r
  rw [← sum_row_card] at hSum
  simp at hSum
  omega

private theorem impossibly_large_row (S : Finset (Fin n × Fin n))
    (hSize : 2 * n < S.card) (hNone : ¬ SameOrientation S)
    (r : Fin n) :
    (row S r).card ≤ 3 := by
  by_contra hLarge
  have hOthers (x : Fin n) (hx : x ∈ (univ : Finset (Fin n)).erase r) :
      (row S x).card ≤ 1 := by
    by_contra hTooLarge
    exact hNone (disjointPairs_of_large S (by
      intro h
      exact (mem_erase.mp hx).1 h.symm) (by omega) (by omega))
  have hSum : (∑ x ∈ (univ : Finset (Fin n)).erase r, (row S x).card) ≤
      ∑ _x ∈ (univ : Finset (Fin n)).erase r, 1 :=
    sum_le_sum hOthers
  have hSplit := sum_erase_add (univ : Finset (Fin n)) (fun x => (row S x).card) (mem_univ r)
  rw [← sum_row_card] at hSplit
  have hr := row_card_le S r
  simp at hSum
  omega

private theorem insideRows_card_le (S : Finset (Fin n × Fin n)) (C : Finset (Fin n))
    (hCol : ∀ x, (row (transpose S) x).card ≤ 3) :
    (S.filter fun p => p.2 ∈ C).card ≤ C.card * 3 := by
  let T := transpose (S.filter fun p => p.2 ∈ C)
  have hRow (c : Fin n) : row T c = if c ∈ C then row (transpose S) c else ∅ := by
    ext r
    by_cases hc : c ∈ C
    · simp [T, hc]
    · simp [T, hc]
  have hSum : (∑ c : Fin n, (row T c).card) ≤
      ∑ c : Fin n, (if c ∈ C then 3 else 0) := by
    apply sum_le_sum
    intro c _
    rw [hRow]
    split <;> simp_all
  rw [← sum_row_card] at hSum
  rw [← sum_filter] at hSum
  simpa [T] using hSum

/-- A selection above both linear bounds contains two disjoint stars
with the same orientation. They can be in rows or in columns. -/
theorem dense_sameOrientation (S : Finset (Fin n × Fin n))
    (hSize : max (2 * n) (n + 6) < S.card) :
    SameOrientation S ∨ SameOrientation (transpose S) := by
  classical
  by_contra hNone
  have hNoRow : ¬ SameOrientation S := fun h => hNone (Or.inl h)
  have hNoCol : ¬ SameOrientation (transpose S) := fun h => hNone (Or.inr h)
  have hLinear := (le_max_left (2 * n) (n + 6)).trans_lt hSize
  have hLinear' := (le_max_right (2 * n) (n + 6)).trans_lt hSize
  have hRow := impossibly_large_row S hLinear hNoRow
  have hCol := impossibly_large_row (transpose S) (by simpa using hLinear) hNoCol
  obtain ⟨r, hr⟩ := dense_row_three S hLinear
  let C := row S r
  have hC : C.card = 3 := Nat.le_antisymm (hRow r) hr
  let T := S.filter fun p => p.2 ∉ C
  let R := T.image Prod.fst
  have hROne (x : Fin n) (hx : x ∈ R) : (row S x).card ≤ 1 := by
    obtain ⟨⟨x', c⟩, hT, rfl⟩ := mem_image.mp hx
    obtain ⟨hCell, hOutside⟩ := mem_filter.mp hT
    change (row S x').card ≤ 1
    by_contra hTwo
    exact hNoRow
      (disjointPairs_of_outside S hr (by omega) ((mem_row S x' c).mpr hCell) hOutside)
  have hT : T.card ≤ R.card := by
    apply Finset.card_le_card_of_injOn Prod.fst (fun x hx => mem_image_of_mem _ hx)
    intro a ha b hb hab
    apply Prod.ext hab
    have hR : a.1 ∈ R := mem_image_of_mem _ ha
    have hOne : ∀ {x y : Fin n}, x ∈ row S a.1 → y ∈ row S a.1 → x = y :=
      card_le_one_iff.mp (hROne a.1 hR)
    apply hOne ((mem_row S a.1 a.2).mpr (mem_filter.mp ha).1)
    apply (mem_row S a.1 b.2).mpr
    simpa [hab] using (mem_filter.mp hb).1
  have hInside := insideRows_card_le S C hCol
  rw [hC] at hInside
  have hSplit := card_filter_add_card_filter_not (s := S) (fun p => p.2 ∈ C)
  have hCount : S.card ≤ 9 + R.card := by
    change (S.filter fun p => p.2 ∈ C).card + T.card = S.card at hSplit
    omega
  have hSumR : (∑ x ∈ R, (row S x).card) ≤ R.card := by
    simpa using (sum_le_sum (fun x hx => hROne x hx) :
      (∑ x ∈ R, (row S x).card) ≤ ∑ _x ∈ R, 1)
  have hSumN : (∑ x ∈ Rᶜ, (row S x).card) ≤ Rᶜ.card * 3 := by
    simpa using (sum_le_sum (fun x _ => hRow x) :
      (∑ x ∈ Rᶜ, (row S x).card) ≤ ∑ _x ∈ Rᶜ, 3)
  have hSum := sum_compl_add_sum R (fun x => (row S x).card)
  rw [← sum_row_card] at hSum
  have hRCard : Rᶜ.card + R.card = n := by
    have hCompl : Rᶜ = univ \ R := by ext x; simp
    rw [hCompl]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (card_sdiff_add_card_eq_card (subset_univ R))
  omega

/-- A row and a column containing stars whose four cells have no cross
adjacency. The row and column intersection lies in neither star. -/
theorem dense_oppositeOrientation (S : Finset (Fin n × Fin n))
    (hSize : 2 * n < S.card) :
    ∃ r c : Fin n, ∃ A B : Finset (Fin n),
      A ⊆ row S r \ {c} ∧ B ⊆ row (transpose S) c \ {r} ∧
      A.card = 2 ∧ B.card = 2 := by
  obtain ⟨r, hr⟩ := dense_row_three S hSize
  obtain ⟨c, hc⟩ := dense_row_three (transpose S) (by simpa using hSize)
  obtain ⟨A, hA, hPairA⟩ := exists_subset_card_eq
    (card_sdiff_ge_two (A := row S r) (B := {c}) (by simpa using hr))
  obtain ⟨B, hB, hPairB⟩ := exists_subset_card_eq
    (card_sdiff_ge_two (A := row (transpose S) c) (B := {r}) (by simpa using hc))
  exact ⟨r, c, A, B, hA, hB, hPairA, hPairB⟩

end EPPAIII.Primitive.RookDensity
