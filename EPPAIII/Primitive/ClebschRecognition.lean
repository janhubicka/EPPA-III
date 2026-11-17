import EPPAIII.Primitive.SmallConstituentSourceModelNormalization
import Mathlib.Logic.Equiv.Option

/-! # Graph recognition for the degree-five Clebsch graph -/

namespace EPPAIII.Primitive

open SimpleGraph

private abbrev ClebschLabel := Option (Fin 5 ⊕ TwoSet (Fin 5))

private def generator : Fin 5 → Nat := ![1, 2, 4, 8, 15]

private def clebschCode : ClebschLabel → Fin 16
  | none => 0
  | some (.inl i) => Fin.ofNat 16 (generator i)
  | some (.inr p) => Fin.ofNat 16 ((List.finRange 5).foldl
      (fun acc i => if i ∈ p.val then acc ^^^ generator i else acc) 0)

private def clebschRelated : ClebschLabel → ClebschLabel → Prop
  | none, some (.inl _) | some (.inl _), none => True
  | some (.inl i), some (.inr p) | some (.inr p), some (.inl i) => i ∈ p.val
  | some (.inr p), some (.inr q) => Disjoint p.val q.val
  | _, _ => False

private instance (a b : ClebschLabel) : Decidable (clebschRelated a b) := by
  rcases a with _ | (i | p) <;> rcases b with _ | (j | q) <;>
    unfold clebschRelated <;> infer_instance

private instance : DecidableRel foldedFiveCubeModel.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (a.val ^^^ b.val) ∈ [1, 2, 4, 8, 15]))

private theorem clebschCode_bijective : Function.Bijective clebschCode := by
  change (∀ a b : ClebschLabel, clebschCode a = clebschCode b → a = b) ∧
    (∀ z : Fin 16, ∃ a : ClebschLabel, clebschCode a = z)
  decide

private theorem clebschCode_adj : ∀ a b : ClebschLabel,
    clebschRelated a b ↔ foldedFiveCubeModel.Adj (clebschCode a) (clebschCode b) := by decide

private theorem clebschCode_degree : ∀ v : Fin 16, foldedFiveCubeModel.degree v = 5 := by decide

private theorem clebsch_no_triangle {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 16 5 0 2) {a b c : V}
    (ab : H.Adj a b) (ac : H.Adj a c) (bc : H.Adj b c) : False := by
  have hPos : 0 < Fintype.card (H.commonNeighbors a b) :=
    Fintype.card_pos_iff.mpr ⟨⟨c, ac, bc⟩⟩
  rw [h.of_adj a b ab] at hPos
  omega

private def splitClebschRoot {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj]
    (r : V) : (H.neighborSet r ⊕ Hᶜ.neighborSet r) ≃ {v : V // v ≠ r} where
  toFun := fun
    | .inl a => ⟨a.val, (H.ne_of_adj a.property).symm⟩
    | .inr b => ⟨b.val, b.property.1.symm⟩
  invFun := fun v => if h : H.Adj r v.val then .inl ⟨v.val, h⟩
    else .inr ⟨v.val, v.property.symm, h⟩
  left_inv := by
    intro x
    rcases x with a | b
    · have ha : H.Adj r a.val := a.property
      simp [ha]
    · have hb : ¬ H.Adj r b.val := b.property.2
      simp [hb]
  right_inv := by
    intro v
    by_cases h : H.Adj r v.val <;> simp [h]

private noncomputable def clebschPair {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 16 5 0 2) {r : V}
    (indices : H.neighborSet r ≃ Fin 5) (v : Hᶜ.neighborSet r) : TwoSet (Fin 5) := by
  let p := Finset.univ.filter (fun i : Fin 5 => H.Adj v.val (indices.symm i).val)
  have hCard : p.card = Fintype.card (H.commonNeighbors r v) := by
    rw [← Fintype.card_coe]
    let e : p ≃ H.commonNeighbors r v :=
      { toFun := fun i => ⟨(indices.symm i.val).val, (indices.symm i.val).property,
          (Finset.mem_filter.mp i.property).2⟩,
        invFun := fun w => ⟨indices ⟨w.val, w.property.1⟩, by
          simpa [p] using (show H.Adj v.val w.val from w.property.2)⟩,
        left_inv := by intro a; ext; simp,
        right_inv := by intro w; ext; simp }
    exact Fintype.card_congr e
  exact ⟨p, hCard.trans (h.of_not_adj v.property.1 v.property.2)⟩

private theorem mem_clebschPair {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 16 5 0 2) {r : V}
    (indices : H.neighborSet r ≃ Fin 5) (v : Hᶜ.neighborSet r) (i : Fin 5) :
    i ∈ (clebschPair H h indices v).val ↔ H.Adj v.val (indices.symm i).val := by
  simp [clebschPair]

private theorem clebschPair_bijective {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 16 5 0 2) {r : V}
    (indices : H.neighborSet r ≃ Fin 5) : Function.Bijective (clebschPair H h indices) := by
  classical
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro p
    have hSize : 1 < p.val.card := by rw [p.property]; decide
    obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp hSize
    let a := indices.symm i
    let b := indices.symm j
    have ha : H.Adj r a := a.property
    have hb : H.Adj r b := b.property
    have hab : a.val ≠ b.val := fun he => hij (indices.symm.injective (Subtype.ext he))
    have hNonedge : ¬ H.Adj a.val b.val := fun hab' => clebsch_no_triangle H h ha hb hab'
    have hCount := h.of_not_adj hab hNonedge
    have hMore : 1 < Fintype.card (H.commonNeighbors a b) := by rw [hCount]; decide
    let first : H.commonNeighbors a b := ⟨r, ha.symm, hb.symm⟩
    obtain ⟨z, hz⟩ := Fintype.exists_ne_of_one_lt_card hMore first
    have hzr : r ≠ z.val := fun he => hz (Subtype.ext he.symm)
    have hNo : ¬ H.Adj r z.val := fun hEdge => clebsch_no_triangle H h ha hEdge z.property.1
    let v : Hᶜ.neighborSet r := ⟨z.val, hzr, hNo⟩
    have leftPair : {i, j} = (clebschPair H h indices v).val := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hxi | hxj
        · rw [hxi]
          exact (mem_clebschPair H h indices v i).mpr z.property.1.symm
        · rw [hxj]
          exact (mem_clebschPair H h indices v j).mpr z.property.2.symm
      · simp [(clebschPair H h indices v).property, hij]
    have rightPair : {i, j} = p.val := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hi
        · exact hj
      · simp [p.property, hij]
    exact ⟨v, Subtype.ext (leftPair.symm.trans rightPair)⟩
  · have hTen : Fintype.card (TwoSet (Fin 5)) = 10 := by decide
    rw [hTen, Hᶜ.card_neighborSet_eq_degree]
    exact h.compl.regular r

/-- The parameters $(16,5,0,2)$ determine the degree-five Clebsch graph.
Name the five neighbours of a point with the five binary generators.
Every remaining vertex has a unique pair of these neighbours. Its
binary label is the sum of their generators. -/
theorem clebsch_iso_of_parameters {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 16 5 0 2) : Nonempty (H ≃g foldedFiveCubeModel) := by
  classical
  obtain ⟨r⟩ : Nonempty V := Fintype.card_pos_iff.mp (by rw [h.card]; decide)
  let indices : H.neighborSet r ≃ Fin 5 := Fintype.equivFinOfCardEq (by
    rw [H.card_neighborSet_eq_degree]
    exact h.regular r)
  let pairs := Equiv.ofBijective _ (clebschPair_bijective H h indices)
  let labels : ClebschLabel ≃ V :=
    (Equiv.optionCongr ((Equiv.sumCongr indices.symm pairs.symm).trans
      (splitClebschRoot H r))).trans (Equiv.optionSubtypeNe r)
  have hLabelAdj (a b : ClebschLabel) (hab : H.Adj (labels a) (labels b)) :
      clebschRelated a b := by
    rcases a with _ | (i | p) <;> rcases b with _ | (j | q)
    · exact (H.ne_of_adj hab rfl).elim
    · trivial
    · exact ((pairs.symm q).property.2 hab).elim
    · trivial
    · exact clebsch_no_triangle H h (indices.symm i).property (indices.symm j).property hab
    · have hm := (mem_clebschPair H h indices (pairs.symm q) i).mpr hab.symm
      change i ∈ (pairs (pairs.symm q)).val at hm
      simpa [clebschRelated] using hm
    · exact ((pairs.symm p).property.2 hab.symm).elim
    · have hm := (mem_clebschPair H h indices (pairs.symm p) j).mpr hab
      change j ∈ (pairs (pairs.symm p)).val at hm
      simpa [clebschRelated] using hm
    · simp only [clebschRelated, Finset.disjoint_left]
      intro i hi hj
      have hi' : i ∈ (clebschPair H h indices (pairs.symm p)).val := by
        change i ∈ (pairs (pairs.symm p)).val
        simpa
      have hj' : i ∈ (clebschPair H h indices (pairs.symm q)).val := by
        change i ∈ (pairs (pairs.symm q)).val
        simpa
      exact clebsch_no_triangle H h hab
        ((mem_clebschPair H h indices (pairs.symm p) i).mp hi')
        ((mem_clebschPair H h indices (pairs.symm q) i).mp hj')
  let e := labels.symm.trans (Equiv.ofBijective _ clebschCode_bijective)
  have hAdj (a b : V) (hab : H.Adj a b) : foldedFiveCubeModel.Adj (e a) (e b) := by
    apply (clebschCode_adj (labels.symm a) (labels.symm b)).mp
    exact hLabelAdj _ _ (by simpa using hab)
  refine ⟨⟨e, ?_⟩⟩
  intro a b
  constructor
  · intro hab
    let f : H.neighborSet a → foldedFiveCubeModel.neighborSet (e a) :=
      fun c => ⟨e c.val, hAdj a c c.property⟩
    have hBij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy)), by
         rw [H.card_neighborSet_eq_degree, foldedFiveCubeModel.card_neighborSet_eq_degree,
           h.regular a, clebschCode_degree]⟩
    obtain ⟨c, hc⟩ := hBij.surjective ⟨e b, hab⟩
    have heq : c.val = b := e.injective (congrArg Subtype.val hc)
    exact heq ▸ c.property
  · exact hAdj a b

open EPPAIII.BlockSystems

/-- The published model identities on `Fin n` other than the Clebsch row,
which is recognized directly from its strongly regular parameters. -/
def PublishedSmallRankThreeModelsExceptClebsch : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p : SRGParameters) (m : SmallConstituentHostModel) (complementModel : Bool),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentSourceModel p = some (m, complementModel) →
    m ≠ .foldedFiveCube →
    Nonempty (H ≃g if complementModel then m.graphᶜ else m.graph)

/-- The 19 remaining source identities suffice for all 20 printed models. -/
theorem publishedSmallRankThreeModels_of_exceptClebsch
    (hSource : PublishedSmallRankThreeModelsExceptClebsch) : PublishedSmallRankThreeModels := by
  intro n H _ p m complementModel hPrim hRank hSRG hLabel
  by_cases hClebsch : m = .foldedFiveCube
  · subst m
    have hParameters : p = ⟨16, 5, 0, 2⟩ ∧ complementModel = false := by
      unfold smallConstituentSourceModel at hLabel
      split at hLabel <;> simp_all
    obtain ⟨rfl, rfl⟩ := hParameters
    change Nonempty (H ≃g foldedFiveCubeModel)
    exact clebsch_iso_of_parameters H hSRG
  · exact hSource H p m complementModel hPrim hRank hSRG hLabel hClebsch

end EPPAIII.Primitive
