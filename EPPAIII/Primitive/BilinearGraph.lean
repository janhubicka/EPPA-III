import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic.FinCases

/-! # The bilinear forms graph on two-row matrices -/

namespace EPPAIII.Primitive

open Matrix

private theorem rank_neg {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin 2) (Fin m) F) : (-A).rank = A.rank := by
  rw [← neg_one_smul F A, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr one_ne_zero))]

/-- Two matrices are adjacent when the difference has rank one. -/
def bilinearFormsGraph (F : Type*) [Field F] (m : ℕ) :
    SimpleGraph (Matrix (Fin 2) (Fin m) F) where
  Adj A B := (A - B).rank = 1
  symm := by
    constructor
    intro A B h
    change (A - B).rank = 1 at h
    rw [← neg_sub A B, rank_neg]
    exact h
  loopless := by
    constructor
    intro A
    change (A - A).rank ≠ 1
    rw [sub_self, Matrix.rank_zero]
    decide

/-- Rank one is the first root constituent. -/
abbrev BilinearRankOne (F : Type*) [Field F] (m : ℕ) :=
    {A : Matrix (Fin 2) (Fin m) F // A.rank = 1}

/-- The graph induced on the rank-one matrices. -/
def bilinearFormsRankOneGraph (F : Type*) [Field F] (m : ℕ) :
    SimpleGraph (BilinearRankOne F m) := (bilinearFormsGraph F m).induce _

/-- The second root constituent consists of the rank-two matrices. -/
abbrev BilinearRankTwo (F : Type*) [Field F] (m : ℕ) :=
    {A : Matrix (Fin 2) (Fin m) F // A.rank = 2}

/-- The graph induced on the rank-two matrices. -/
def bilinearFormsRankTwoGraph (F : Type*) [Field F] (m : ℕ) :
    SimpleGraph (BilinearRankTwo F m) := (bilinearFormsGraph F m).induce _

private theorem matrix_rank_nonzero_of_ne_zero {F : Type*} [Field F] {m : ℕ}
    {A : Matrix (Fin 2) (Fin m) F} (hA : A ≠ 0) : A.rank ≠ 0 := by
  intro hRank
  apply hA
  have hSpan : Submodule.span F (Set.range A.row) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    rwa [← Matrix.rank_eq_finrank_span_row]
  ext i j
  have hRow : A.row i ∈ Submodule.span F (Set.range A.row) :=
    Submodule.subset_span ⟨i, rfl⟩
  rw [hSpan, Submodule.mem_bot] at hRow
  exact congrFun hRow j

/-- The neighbours of the zero matrix are exactly the rank-one matrices. -/
theorem bilinearFormsGraph_zero_adj_iff {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin 2) (Fin m) F) :
    (bilinearFormsGraph F m).Adj 0 A ↔ A.rank = 1 := by
  change (0 - A).rank = 1 ↔ A.rank = 1
  rw [zero_sub, rank_neg]

/-- The nonzero nonneighbours of zero are exactly the rank-two matrices. -/
theorem bilinearFormsGraph_zero_nonadj_iff {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin 2) (Fin m) F) :
    (A ≠ 0 ∧ ¬ (bilinearFormsGraph F m).Adj 0 A) ↔ A.rank = 2 := by
  rw [bilinearFormsGraph_zero_adj_iff]
  constructor
  · rintro ⟨hA, hNotOne⟩
    have hnz := matrix_rank_nonzero_of_ne_zero hA
    have hBound : A.rank ≤ 2 := by simpa using A.rank_le_card_height
    omega
  · intro hrank
    refine ⟨fun h => ?_, by omega⟩
    rw [h, Matrix.rank_zero] at hrank
    contradiction

/-- A two-row matrix has rank two precisely when its ordered rows are independent. -/
theorem bilinear_rank_two_iff_rows_independent {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin 2) (Fin m) F) : A.rank = 2 ↔ LinearIndependent F A.row := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
    ← Matrix.rank_eq_finrank_span_row]
  simp [eq_comm]

/-- The rank-two constituent has `(q^m−1)(q^m−q)` vertices. -/
theorem bilinearFormsRankTwo_card {F : Type*} [Field F] [Fintype F] {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (BilinearRankTwo F m) = (Fintype.card F ^ m - 1) *
      (Fintype.card F ^ m - Fintype.card F) := by
  let e : BilinearRankTwo F m ≃ {A : Fin 2 → (Fin m → F) // LinearIndependent F A} :=
    ⟨fun A => ⟨A.val, (bilinear_rank_two_iff_rows_independent A.val).mp A.property⟩,
      fun A => ⟨A.val, (bilinear_rank_two_iff_rows_independent A.val).mpr A.property⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Nat.card_congr e]
  have hDimension : Module.finrank F (Fin m → F) = m := by simp
  have hCount := card_linearIndependent (K := F) (V := Fin m → F)
    (show 2 ≤ Module.finrank F (Fin m → F) by rwa [hDimension])
  simpa [hDimension, Fin.prod_univ_two] using hCount

/-- Column spaces are distinct on an independent set in the rank-one
constituent, and there are exactly q+1 one-dimensional column spaces. -/
theorem bilinearFormsRankOne_independent_bound {F : Type*} [Field F] [Fintype F]
    {m k : ℕ} (f : Fin k ↪ BilinearRankOne F m)
    (hIndependent : ∀ a b, ¬ (bilinearFormsRankOneGraph F m).Adj (f a) (f b)) :
    k ≤ Fintype.card F + 1 := by
  classical
  let columnSpace (A : BilinearRankOne F m) := Submodule.span F (Set.range A.val.col)
  have hDimension (A : BilinearRankOne F m) : Module.finrank F (columnSpace A) = 1 :=
    (Matrix.rank_eq_finrank_span_cols A.val).symm.trans A.property
  let point (i : Fin k) : Projectivization F (Fin 2 → F) :=
    Projectivization.mk'' (columnSpace (f i)) (hDimension (f i))
  have hInjective : Function.Injective point := by
    intro i j hij
    by_contra hne
    have hs : columnSpace (f i) = columnSpace (f j) := by
      simpa only [point, Projectivization.submodule_mk''] using
        congrArg Projectivization.submodule hij
    have hmat : (f i).val ≠ (f j).val := fun h => hne (f.injective (Subtype.ext h))
    have hSpan : Submodule.span F (Set.range ((f i).val - (f j).val).col) ≤ columnSpace (f i) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨c, rfl⟩
      apply Submodule.sub_mem
      · exact Submodule.subset_span ⟨c, rfl⟩
      · rw [hs]
        exact Submodule.subset_span ⟨c, rfl⟩
    have hUpper : ((f i).val - (f j).val).rank ≤ 1 := by
      rw [Matrix.rank_eq_finrank_span_cols]
      exact (Submodule.finrank_mono hSpan).trans_eq (hDimension (f i))
    have hNonzero := matrix_rank_nonzero_of_ne_zero (sub_ne_zero.mpr hmat)
    apply hIndependent i j
    change ((f i).val - (f j).val).rank = 1
    omega
  let : Fintype (Projectivization F (Fin 2 → F)) := Fintype.ofFinite _
  have hCard : Fintype.card (Projectivization F (Fin 2 → F)) = Fintype.card F + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Projectivization.card_of_finrank_two F _ (by simp)
  simpa [hCard] using Fintype.card_le_of_injective point hInjective

/-- Distinct matrices with a common row differ by a nonzero matrix supported
on the other row and are therefore adjacent. -/
theorem bilinearFormsGraph_adj_of_same_row {F : Type*} [Field F] {m : ℕ}
    {A B : Matrix (Fin 2) (Fin m) F} (r : Fin 2) (hAB : A ≠ B) (hRow : A r = B r) :
    (bilinearFormsGraph F m).Adj A B := by
  have hDiff : A - B ≠ 0 := sub_ne_zero.mpr hAB
  have hSupport : Function.support (A - B).row ⊆ (Finset.univ.erase r : Finset (Fin 2)) := by
    intro i hi
    apply Finset.mem_erase.mpr
    refine ⟨fun h => ?_, Finset.mem_univ i⟩
    subst i
    apply Function.mem_support.mp hi
    ext j
    change A r j - B r j = 0
    exact sub_eq_zero.mpr (congrFun hRow j)
  have hCard : (Finset.univ.erase r).card = 1 := by simp
  have hRank : (A - B).rank ≤ 1 := by
    simpa only [hCard] using Matrix.rank_le_card_of_support_subset (A - B) _ hSupport
  have hnz := matrix_rank_nonzero_of_ne_zero hDiff
  change (A - B).rank = 1
  omega

/-- First rows are distinct on an independent set in the rank-two constituent.
This proves the cardinal upper bound used in the bilinear exclusion. -/
theorem bilinearFormsRankTwo_independent_bound {F : Type*} [Field F] [Fintype F]
    {m k : ℕ} (f : Fin k ↪ BilinearRankTwo F m)
    (hIndependent : ∀ a b, ¬ (bilinearFormsRankTwoGraph F m).Adj (f a) (f b)) :
    k ≤ Fintype.card F ^ m := by
  let row (a : Fin k) : Fin m → F := (f a).val 0
  have hInjective : Function.Injective row := by
    intro a b hrow
    by_contra hne
    have hmat : (f a).val ≠ (f b).val := fun h => hne (f.injective (Subtype.ext h))
    exact hIndependent a b (bilinearFormsGraph_adj_of_same_row 0 hmat hrow)
  simpa [Fintype.card_pi_const] using Fintype.card_le_of_injective row hInjective

/-- A common second row outside the span of the two first rows connects
any two rank-two matrices by changes of individual rows. -/
theorem bilinearFormsRankTwo_connected {F : Type*} [Field F] {m : ℕ} (hm : 3 ≤ m) :
    (bilinearFormsRankTwoGraph F m).Connected := by
  classical
  have hDimension : Module.finrank F (Fin m → F) = m := by simp
  refine @SimpleGraph.Connected.mk (BilinearRankTwo F m) (bilinearFormsRankTwoGraph F m) ?_ ?_
  · intro A B
    let rows : Fin 2 → (Fin m → F) := ![A.val 0, B.val 0]
    let S := Submodule.span F (Set.range rows)
    have hSmall : Module.finrank F S ≤ 2 := by
      simpa [S, Set.finrank] using (finrank_range_le_card (R := F) rows)
    have hNotTop : S ≠ ⊤ := ne_of_lt (Submodule.lt_top_of_finrank_lt_finrank (by omega))
    obtain ⟨z, hz⟩ : ∃ z, z ∉ S := by
      by_contra! h
      exact hNotTop (Submodule.eq_top_iff'.mpr h)
    have hRank (r : Fin m → F) (hr : r ≠ 0) (hS : r ∈ S) :
        (Matrix.of ![r, z]).rank = 2 := by
      apply (bilinear_rank_two_iff_rows_independent _).mpr
      change LinearIndependent F ![r, z]
      apply (LinearIndependent.pair_iff' hr).mpr
      intro c hc
      exact hz (hc ▸ S.smul_mem c hS)
    have ha : A.val 0 ≠ 0 := ((bilinear_rank_two_iff_rows_independent _).mp A.property).ne_zero 0
    have hb : B.val 0 ≠ 0 := ((bilinear_rank_two_iff_rows_independent _).mp B.property).ne_zero 0
    let A' : BilinearRankTwo F m := ⟨Matrix.of ![A.val 0, z],
      hRank _ ha (Submodule.subset_span ⟨0, rfl⟩)⟩
    let B' : BilinearRankTwo F m := ⟨Matrix.of ![B.val 0, z],
      hRank _ hb (Submodule.subset_span ⟨1, rfl⟩)⟩
    have hStep (C D : BilinearRankTwo F m) (r : Fin 2) (h : C.val r = D.val r) :
        (bilinearFormsRankTwoGraph F m).Reachable C D := by
      by_cases hEq : C = D
      · subst D
        exact SimpleGraph.Reachable.rfl
      · have hAdj : (bilinearFormsRankTwoGraph F m).Adj C D :=
          bilinearFormsGraph_adj_of_same_row r (fun e => hEq (Subtype.ext e)) h
        exact hAdj.reachable
    exact (hStep A A' 0 rfl).trans ((hStep A' B' 1 rfl).trans (hStep B' B 0 rfl))
  · let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, by omega⟩
    have hij : i ≠ j := fun e => Nat.zero_ne_one (congrArg Fin.val e)
    let b := Pi.basisFun F (Fin m)
    have hInjective : Function.Injective (![i, j] : Fin 2 → Fin m) := by
      intro u v h
      fin_cases u <;> fin_cases v <;> simp_all
    have hIndependent : LinearIndependent F ![b i, b j] := by
      convert b.linearIndependent.comp ![i, j] hInjective using 1
      ext k
      fin_cases k <;> rfl
    exact ⟨⟨Matrix.of ![b i, b j], (bilinear_rank_two_iff_rows_independent _).mpr hIndependent⟩⟩

end EPPAIII.Primitive
