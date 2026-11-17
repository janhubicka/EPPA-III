import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fin.VecNotation

/-! # Two pentagons in the alternating chart of the half-spin graph -/

namespace EPPAIII.Primitive

open Matrix

/-- Alternating matrices, including in characteristic two. -/
def IsAlternatingFive {R : Type*} [Ring R] (A : Matrix (Fin 5) (Fin 5) R) : Prop :=
  (∀ i, A i i = 0) ∧ ∀ i j, A i j = -A j i

abbrev HalfSpinChartVertex (F : Type*) [Field F] :=
  {A : Matrix (Fin 5) (Fin 5) F // IsAlternatingFive A ∧ A.rank % 2 = 0}

/-- The origin of the alternating chart corresponds to the fixed maximal
totally singular space. -/
def halfSpinChartOrigin (F : Type*) [Field F] : HalfSpinChartVertex F :=
  ⟨0, by simp [IsAlternatingFive]⟩

/-- The chart adjacency is intersection in dimension three, expressed as the
rank of a difference. -/
def halfSpinChartGraph (F : Type*) [Field F] : SimpleGraph (HalfSpinChartVertex F) where
  Adj A B := (A.val - B.val).rank = 2
  symm := by
    constructor
    intro A B h
    change (A.val - B.val).rank = 2 at h
    rw [← neg_sub A.val B.val, ← neg_one_smul F (A.val - B.val),
      Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr one_ne_zero))]
    exact h
  loopless := by
    constructor
    intro A
    change (A.val - A.val).rank ≠ 2
    rw [sub_self, Matrix.rank_zero]
    decide

private abbrev IntegerForm := Matrix (Fin 5) (Fin 5) ℤ

private def wedge {R : Type*} [Ring R] (u v : Fin 5 → R) :
    Matrix (Fin 5) (Fin 5) R :=
  Matrix.of fun i j => u i * v j - v i * u j

private theorem wedge_alternating {R : Type*} [CommRing R] (u v : Fin 5 → R) :
    IsAlternatingFive (wedge u v) := by
  constructor
  · intro i
    simp [wedge, mul_comm]
  · intro i j
    simp only [wedge, Matrix.of_apply]
    ring

private theorem alternating_add {R : Type*} [Ring R] {A B : Matrix (Fin 5) (Fin 5) R}
    (hA : IsAlternatingFive A) (hB : IsAlternatingFive B) : IsAlternatingFive (A + B) := by
  constructor
  · intro i
    simp [hA.1 i, hB.1 i]
  · intro i j
    simp only [Matrix.add_apply, neg_add_rev]
    rw [hA.2 i j, hB.2 i j, add_comm]

private def unitVector (i : Fin 5) : Fin 5 → ℤ := fun j => if j = i then 1 else 0

private def pencil (i : Fin 5) : IntegerForm :=
  wedge (unitVector i) (unitVector (i + 1))

private def offset : IntegerForm :=
  wedge (unitVector 0) (unitVector 2) + wedge (unitVector 1) (unitVector 3)

private def seed (shifted : Bool) (i : Fin 5) : IntegerForm :=
  if shifted then offset + pencil i else pencil i

private theorem seed_alternating (shifted : Bool) (i : Fin 5) : IsAlternatingFive (seed shifted i) := by
  unfold seed offset pencil
  split
  · exact alternating_add (alternating_add (wedge_alternating ..) (wedge_alternating ..))
      (wedge_alternating ..)
  · exact wedge_alternating ..

private def liftForm (F : Type*) [Field F] (A : IntegerForm) :
    Matrix (Fin 5) (Fin 5) F := A.map (Int.castRingHom F)

private theorem liftForm_sub {F : Type*} [Field F] (A B : IntegerForm) :
    liftForm F (A - B) = liftForm F A - liftForm F B := by
  ext i j
  simp [liftForm, Int.cast_sub]

private theorem liftForm_alternating {F : Type*} [Field F] {A : IntegerForm}
    (h : IsAlternatingFive A) : IsAlternatingFive (liftForm F A) := by
  constructor
  · intro i
    simp [liftForm, h.1 i]
  · intro i j
    change (A i j : F) = -(A j i : F)
    rw [h.2 i j, Int.cast_neg]

private theorem liftWedge_rank_le_two {F : Type*} [Field F] (u v : Fin 5 → ℤ) :
    (liftForm F (wedge u v)).rank ≤ 2 := by
  let L : Matrix (Fin 5) (Fin 2) F := Matrix.of fun i => ![(u i : F), (v i : F)]
  let R : Matrix (Fin 2) (Fin 5) F := Matrix.of fun k j => ![(v j : F), -(u j : F)] k
  have hFactor : liftForm F (wedge u v) = L * R := by
    ext i j
    simp [liftForm, wedge, L, R, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  rw [hFactor]
  exact (Matrix.rank_mul_le_left L R).trans (Matrix.rank_le_width L)

private theorem liftForm_rank_of_minor {F : Type*} [Field F] {d : ℕ}
    (A : IntegerForm) (u : Fin d → Fin 5)
    (h : (A.submatrix u u).det = 1) : d ≤ (liftForm F A).rank := by
  have hDet : ((liftForm F A).submatrix u u).det = 1 := by
    change (((A.map (Int.castRingHom F)).submatrix u u)).det = 1
    rw [Matrix.submatrix_map]
    convert ((Int.castRingHom F).map_det (A.submatrix u u)).symm using 1
    · congr 1
    · rw [h, map_one]
  have hRank := Matrix.rank_of_det_ne_zero (hDet ▸ (one_ne_zero : (1 : F) ≠ 0))
  simpa only [hRank, Fintype.card_fin] using
    Matrix.rank_submatrix_le (liftForm F A) u u

private def smallMinor (i : Fin 5) : Fin 2 → Fin 5 := ![i, i + 1]

private theorem pencil_minor : ∀ i : Fin 5, ((pencil i).submatrix (smallMinor i) (smallMinor i)).det = 1 := by
  decide

private theorem pencil_sub_minor : ∀ i j : Fin 5, i ≠ j →
    ((pencil i - pencil j).submatrix (smallMinor i) (smallMinor i)).det = 1 := by
  decide

private theorem shifted_minor : ∀ i : Fin 5,
    (((seed true i).submatrix (Fin.castLE (by decide : 4 ≤ 5))
      (Fin.castLE (by decide : 4 ≤ 5))).det = 1) := by
  decide

private def jointMinor (i j : Fin 5) : Fin 4 → Fin 5 := ![i, i + 1, j, j + 1]

private theorem nonedge_minor : ∀ i j : Fin 5, i ≠ j → ¬ (SimpleGraph.cycleGraph 5).Adj i j →
    ((pencil i - pencil j).submatrix (jointMinor i j) (jointMinor i j)).det = 1 := by
  decide

private def sharedVector (i j : Fin 5) : Fin 5 → ℤ :=
  if j = i + 1 then unitVector (i + 1) else - unitVector (j + 1)

private def outsideVector (i j : Fin 5) : Fin 5 → ℤ :=
  if j = i + 1 then unitVector i + unitVector (i + 2)
  else unitVector j + unitVector (j + 2)

private def checkEdgeFactor (p : Fin 5 × Fin 5 × Fin 5 × Fin 5) : Bool :=
  if (SimpleGraph.cycleGraph 5).Adj p.1 p.2.1 then
    decide ((pencil p.1 - pencil p.2.1) p.2.2.1 p.2.2.2 =
      wedge (outsideVector p.1 p.2.1) (sharedVector p.1 p.2.1) p.2.2.1 p.2.2.2)
  else true

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
private theorem edge_factor_checked : ∀ p, checkEdgeFactor p = true := by
  decide

private theorem edge_factor_coordinates (i j r c : Fin 5) (h : (SimpleGraph.cycleGraph 5).Adj i j) :
    (pencil i - pencil j) r c = wedge (outsideVector i j) (sharedVector i j) r c := by
  apply of_decide_eq_true
  simpa only [checkEdgeFactor, ite_eq_left h] using edge_factor_checked (i, j, r, c)

private theorem pencil_rank {F : Type*} [Field F] (i : Fin 5) :
    (liftForm F (pencil i)).rank = 2 :=
  le_antisymm (liftWedge_rank_le_two ..) (liftForm_rank_of_minor _ _ (pencil_minor i))

private theorem pencil_sub_rank {F : Type*} [Field F] (i j : Fin 5)
    (h : (SimpleGraph.cycleGraph 5).Adj i j) : (liftForm F (pencil i - pencil j)).rank = 2 := by
  apply le_antisymm _ (liftForm_rank_of_minor _ _ (pencil_sub_minor i j h.ne))
  rw [show pencil i - pencil j = wedge (outsideVector i j) (sharedVector i j) from
    Matrix.ext (fun r c => edge_factor_coordinates i j r c h)]
  exact liftWedge_rank_le_two ..

private def shiftedNull (i : Fin 5) : Fin 5 → ℤ :=
  ![0, if i = 3 then 1 else 0, if i = 4 then 1 else 0, 0, 1]

private theorem shiftedNull_coefficients :
    ∀ i j : Fin 5, (seed true i).mulVec (shiftedNull i) j = 0 := by
  decide

private theorem shifted_rank {F : Type*} [Field F] (i : Fin 5) :
    (liftForm F (seed true i)).rank = 4 := by
  let A := liftForm F (seed true i)
  let x : Fin 5 → F := fun j => (shiftedNull i j : F)
  have hx : x ≠ 0 := by
    intro h
    have h4 := congrFun h (4 : Fin 5)
    simp [x, shiftedNull] at h4
  have hKer : x ∈ LinearMap.ker A.mulVecLin := by
    apply LinearMap.mem_ker.mpr
    funext j
    change (∑ k, (seed true i j k : F) * (shiftedNull i k : F)) = 0
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero, Matrix.mulVec, dotProduct] using
      congrArg (Int.cast : ℤ → F) (shiftedNull_coefficients i j)
  have hKerPos : 0 < Module.finrank F (LinearMap.ker A.mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨x, hKer⟩, fun h => hx (congrArg Subtype.val h)⟩
  have hDimension := A.mulVecLin.finrank_range_add_finrank_ker
  change A.rank + _ = Module.finrank F (Fin 5 → F) at hDimension
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hDimension
  have hLower : 4 ≤ A.rank := liftForm_rank_of_minor _ _ (shifted_minor i)
  dsimp only [A] at hDimension hLower hKerPos
  omega

private def seedPoint (F : Type*) [Field F] (shifted : Bool) (i : Fin 5) : HalfSpinChartVertex F :=
  ⟨liftForm F (seed shifted i), liftForm_alternating (seed_alternating shifted i), by
    cases shifted
    · change (liftForm F (pencil i)).rank % 2 = 0
      rw [pencil_rank]
    · rw [shifted_rank]⟩

private theorem seed_sub (shifted : Bool) (i j : Fin 5) :
    seed shifted i - seed shifted j = pencil i - pencil j := by
  cases shifted
  · rfl
  · simp [seed]

private theorem seedPoint_ne {F : Type*} [Field F] (shifted : Bool) {i j : Fin 5}
    (hij : i ≠ j) : seedPoint F shifted i ≠ seedPoint F shifted j := by
  intro h
  have hEq : liftForm F (seed shifted i) = liftForm F (seed shifted j) := congrArg Subtype.val h
  have hZero : liftForm F (pencil i - pencil j) = 0 := by
    rw [← seed_sub shifted, liftForm_sub, hEq, sub_self]
  have hRank : 2 ≤ (liftForm F (pencil i - pencil j)).rank :=
    liftForm_rank_of_minor _ _ (pencil_sub_minor i j hij)
  rw [hZero, Matrix.rank_zero] at hRank
  exact (by decide : ¬ (2 ≤ 0)) hRank

private def seedPentagon (F : Type*) [Field F] (shifted : Bool) :
    SimpleGraph.cycleGraph 5 ↪g halfSpinChartGraph F where
  toFun := seedPoint F shifted
  inj' := fun _ _ h => Classical.byContradiction fun hn => seedPoint_ne shifted hn h
  map_rel_iff' := by
    intro i j
    change (liftForm F (seed shifted i) - liftForm F (seed shifted j)).rank = 2 ↔ _
    rw [← liftForm_sub, seed_sub]
    refine ⟨fun h => ?_, pencil_sub_rank i j⟩
    by_contra hNon
    by_cases hEq : i = j
    · subst j
      simp [liftForm] at h
    · have hRank : 4 ≤ (liftForm F (pencil i - pencil j)).rank :=
        liftForm_rank_of_minor _ _ (nonedge_minor i j hEq hNon)
      rw [h] at hRank
      exact (by decide : ¬ (4 ≤ 2)) hRank

/-- The consecutive elementary alternating forms give a pentagon among the
neighbours of the chart origin. -/
def halfSpinChart_localPentagon (F : Type*) [Field F] :
    SimpleGraph.cycleGraph 5 ↪g
      (halfSpinChartGraph F).induce ((halfSpinChartGraph F).neighborSet (halfSpinChartOrigin F)) where
  toFun i := ⟨seedPoint F false i, by
    change (0 - liftForm F (pencil i)).rank = 2
    rw [zero_sub, ← neg_one_smul F (liftForm F (pencil i)),
      Matrix.rank_smul_of_mem_nonZeroDivisors _
        (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr one_ne_zero)), pencil_rank]⟩
  inj' := fun _ _ h => (seedPentagon F false).injective (congrArg Subtype.val h)
  map_rel_iff' := (seedPentagon F false).map_rel_iff'

/-- One common translate of the pencil gives a pentagon among the distinct
nonneighbours of the chart origin. -/
def halfSpinChart_nonlocalPentagon (F : Type*) [Field F] :
    SimpleGraph.cycleGraph 5 ↪g
      (halfSpinChartGraph F).induce {x | halfSpinChartOrigin F ≠ x ∧
        ¬ (halfSpinChartGraph F).Adj (halfSpinChartOrigin F) x} where
  toFun i := ⟨seedPoint F true i, by
    have hRank : 4 ≤ (liftForm F (seed true i)).rank :=
      liftForm_rank_of_minor _ _ (shifted_minor i)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hZero : 0 = liftForm F (seed true i) := congrArg Subtype.val h
      rw [← hZero, Matrix.rank_zero] at hRank
      exact (by decide : ¬ (4 ≤ 0)) hRank
    · change (0 - liftForm F (seed true i)).rank = 2 at h
      rw [zero_sub, ← neg_one_smul F (liftForm F (seed true i)),
        Matrix.rank_smul_of_mem_nonZeroDivisors _
          (mem_nonZeroDivisors_of_ne_zero (neg_ne_zero.mpr one_ne_zero))] at h
      rw [h] at hRank
      exact (by decide : ¬ (4 ≤ 2)) hRank⟩
  inj' := fun _ _ h => (seedPentagon F true).injective (congrArg Subtype.val h)
  map_rel_iff' := (seedPentagon F true).map_rel_iff'

end EPPAIII.Primitive
