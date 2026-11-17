import EPPAIII.Primitive.BilinearGraph

/-! # Rank-one matrices in the two-row bilinear forms graph -/

namespace EPPAIII.Primitive

open Matrix

/-- The second row of a rank-one matrix with a nonzero first row is a
scalar multiple of the first row. -/
theorem bilinear_rank_one_iff_rows_proportional {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin 2) (Fin m) F) (h : A 0 ≠ 0) :
    A.rank = 1 ↔ ∃ c : F, c • A 0 = A 1 := by
  have hn : A ≠ 0 := fun e => h (congrArg (fun M : Matrix (Fin 2) (Fin m) F => M 0) e)
  have hbound : A.rank ≤ 2 := by simpa using A.rank_le_card_height
  have hzero : A.rank ≠ 0 := by
    intro hr
    have ha : ¬ (bilinearFormsGraph F m).Adj 0 A := by
      rw [bilinearFormsGraph_zero_adj_iff, hr]
      decide
    exact (by omega : ¬ A.rank = 2) ((bilinearFormsGraph_zero_nonadj_iff A).mp ⟨hn, ha⟩)
  have htwo : A.rank = 2 ↔ ∀ c : F, c • A 0 ≠ A 1 := by
    rw [bilinear_rank_two_iff_rows_independent]
    have hrows : A.row = ![A 0, A 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hrows, LinearIndependent.pair_iff' h]
  constructor
  · intro hr
    by_contra! hp
    have := htwo.mpr hp
    omega
  · rintro ⟨c, hc⟩
    have hntwo : A.rank ≠ 2 := fun e => htwo.mp e c hc
    omega

/-- Construct a two-row matrix in one normalized column direction. -/
def bilinearRankOneMatrix {F : Type*} [Field F] {m : ℕ} (c : Option F)
    (v : Fin m → F) : Matrix (Fin 2) (Fin m) F :=
  Matrix.of (match c with | none => ![0, v] | some a => ![v, a • v])

private theorem bilinearRankOneMatrix_has_rank_one {F : Type*} [Field F] {m : ℕ}
    (c : Option F) {v : Fin m → F} (hv : v ≠ 0) :
    (bilinearRankOneMatrix c v).rank = 1 := by
  cases c with
  | none =>
      have hn : (0 : Matrix (Fin 2) (Fin m) F) ≠ bilinearRankOneMatrix none v := by
        intro h
        exact hv ((congrArg (fun M : Matrix (Fin 2) (Fin m) F => M 1) h).symm)
      exact (bilinearFormsGraph_zero_adj_iff (bilinearRankOneMatrix none v)).mp
        (bilinearFormsGraph_adj_of_same_row 0 hn rfl)
  | some a =>
      exact (bilinear_rank_one_iff_rows_proportional (bilinearRankOneMatrix (some a) v) hv).mpr ⟨a, rfl⟩

/-- A rank-one matrix is determined uniquely by a projective column direction
and the nonzero row obtained using its normalized representative. The
vertical direction has code `none`, and the direction `(1,c)` has code
`some c`. -/
noncomputable def bilinearRankOneEquiv {F : Type*} [Field F] {m : ℕ} :
    (Option F × {v : Fin m → F // v ≠ 0}) ≃ BilinearRankOne F m := by
  classical
  let f (u : Option F × {v : Fin m → F // v ≠ 0}) : BilinearRankOne F m :=
    ⟨bilinearRankOneMatrix u.1 u.2.val, bilinearRankOneMatrix_has_rank_one u.1 u.2.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro ⟨c, v⟩ ⟨d, w⟩ h
    have hM : bilinearRankOneMatrix c v.val = bilinearRankOneMatrix d w.val :=
      congrArg Subtype.val h
    have h₀ := congrArg (fun M : Matrix (Fin 2) (Fin m) F => M 0) hM
    have h₁ := congrArg (fun M : Matrix (Fin 2) (Fin m) F => M 1) hM
    cases c with
    | none =>
        cases d with
        | none => exact Prod.ext rfl (Subtype.ext h₁)
        | some d => exact (w.property h₀.symm).elim
    | some c =>
        cases d with
        | none => exact (v.property h₀).elim
        | some d =>
            have hrow : v = w := Subtype.ext h₀
            subst w
            exact Prod.ext (congrArg some (smul_left_injective F v.property h₁)) rfl
  · intro ⟨A, hA⟩
    by_cases ha : A 0 = 0
    · have hb : A 1 ≠ 0 := by
        intro h
        have hzero : A = 0 := by
          ext i j
          fin_cases i
          · exact congrFun ha j
          · exact congrFun h j
        rw [hzero, Matrix.rank_zero] at hA
        omega
      refine ⟨(none, ⟨A 1, hb⟩), Subtype.ext ?_⟩
      ext i j
      fin_cases i
      · exact congrFun ha.symm j
      · rfl
    · obtain ⟨c, hc⟩ := (bilinear_rank_one_iff_rows_proportional A ha).mp hA
      refine ⟨(some c, ⟨A 0, ha⟩), Subtype.ext ?_⟩
      ext i j
      fin_cases i
      · rfl
      · exact congrFun hc j

theorem bilinearRankOneEquiv_val {F : Type*} [Field F] {m : ℕ}
    (c : Option F) (v : {v : Fin m → F // v ≠ 0}) :
    (bilinearRankOneEquiv (c, v)).val = bilinearRankOneMatrix c v.val := rfl

/-- The rank-one constituent has `(q+1)(q^m−1)` vertices. -/
theorem bilinearFormsRankOne_card {F : Type*} [Field F] [Fintype F] {m : ℕ} :
    Nat.card (BilinearRankOne F m) = (Fintype.card F + 1) * (Fintype.card F ^ m - 1) := by
  classical
  rw [← Nat.card_congr bilinearRankOneEquiv]
  have hzero : Fintype.card {v : Fin m → F // v = 0} = 1 :=
    Fintype.card_unique
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_option,
    Fintype.card_subtype_compl (fun v : Fin m → F => v = 0), hzero,
    Fintype.card_fun, Fintype.card_fin]

private theorem reachable_same_column {F : Type*} [Field F] {m : ℕ}
    (c : Option F) (v w : {v : Fin m → F // v ≠ 0}) :
    (bilinearFormsRankOneGraph F m).Reachable
      (bilinearRankOneEquiv (c, v)) (bilinearRankOneEquiv (c, w)) := by
  by_cases h : v = w
  · rw [h]
  · have hsub : v.val - w.val ≠ 0 := sub_ne_zero.mpr (fun h' => h (Subtype.ext h'))
    apply SimpleGraph.Adj.reachable
    change (bilinearFormsGraph F m).Adj (bilinearRankOneMatrix c v.val) (bilinearRankOneMatrix c w.val)
    cases c with
    | none =>
        have hn : bilinearRankOneMatrix none v.val ≠ bilinearRankOneMatrix none w.val := by
          intro he
          exact h (Subtype.ext (congrArg (fun A : Matrix (Fin 2) (Fin m) F => A 1) he))
        exact bilinearFormsGraph_adj_of_same_row 0 hn rfl
    | some c =>
        let D := bilinearRankOneMatrix (some c) v.val - bilinearRankOneMatrix (some c) w.val
        change D.rank = 1
        refine (bilinear_rank_one_iff_rows_proportional D hsub).mpr ⟨c, ?_⟩
        change c • (v.val - w.val) = c • v.val - c • w.val
        rw [smul_sub]

private theorem reachable_same_row {F : Type*} [Field F] {m : ℕ}
    (c d : Option F) (v : {v : Fin m → F // v ≠ 0}) :
    (bilinearFormsRankOneGraph F m).Reachable
      (bilinearRankOneEquiv (c, v)) (bilinearRankOneEquiv (d, v)) := by
  have hfirst (a : F) :
      (bilinearFormsRankOneGraph F m).Adj
        (bilinearRankOneEquiv (some a, v)) (bilinearRankOneEquiv (none, v)) := by
    let D := bilinearRankOneMatrix (some a) v.val - bilinearRankOneMatrix (none : Option F) v.val
    change D.rank = 1
    have hrow : D 0 = v.val := sub_zero _
    refine (bilinear_rank_one_iff_rows_proportional D (hrow ▸ v.property)).mpr ⟨a - 1, ?_⟩
    rw [hrow]
    change (a - 1) • v.val = a • v.val - v.val
    rw [sub_smul, one_smul]
  cases c with
  | none =>
      cases d with
      | none => exact .rfl
      | some b => exact (hfirst b).symm.reachable
  | some a =>
      cases d with
      | none => exact (hfirst a).reachable
      | some b => exact (hfirst a).reachable.trans (hfirst b).symm.reachable

/-- The rank-one constituent is connected whenever there is a nonzero row. -/
theorem bilinearFormsRankOne_connected {F : Type*} [Field F] {m : ℕ} (hm : 0 < m) :
    (bilinearFormsRankOneGraph F m).Connected := by
  refine @SimpleGraph.Connected.mk (BilinearRankOne F m) (bilinearFormsRankOneGraph F m) ?_ ?_
  · intro A B
    obtain ⟨⟨c, v⟩, rfl⟩ := bilinearRankOneEquiv.surjective A
    obtain ⟨⟨d, w⟩, rfl⟩ := bilinearRankOneEquiv.surjective B
    exact (reachable_same_column c v w).trans (reachable_same_row c d w)
  · let v : Fin m → F := fun _ => 1
    have hv : v ≠ 0 := fun h => one_ne_zero (congrFun h ⟨0, hm⟩)
    exact ⟨bilinearRankOneEquiv (none, ⟨v, hv⟩)⟩

end EPPAIII.Primitive
