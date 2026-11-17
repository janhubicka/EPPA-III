import EPPAIII.Primitive.RankThreeActionCatalogue
import EPPAIII.Primitive.SmallConstituentModels
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! # Recognition of the four small Paley hosts from their permutation actions -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

/-- A rank-three subgroup with a vertex labelling by a field, in which
each permutation is semilinear with a nonzero square multiplier. -/
def HasPaleyRankThreeAction {V : Type*} (H : SimpleGraph V) (F : Type*) [Field F] : Prop :=
  ∃ (labels : V ≃ F) (P : Subgroup (Equiv.Perm V)), HasRankThreeGraphOrbits P H ∧
    ∀ p : P, ∃ (a b : F) (σ : F ≃+* F), IsSquare a ∧ a ≠ 0 ∧
      ∀ z, labels (p.val z) = a * σ (labels z) + b

private theorem square_sub_or_iff {F : Type*} [Field F]
    (hNeg : IsSquare (-1 : F)) (x y : F) :
    (IsSquare (x - y) ∨ IsSquare (y - x)) ↔ IsSquare (x - y) := by
  constructor
  · rintro (h | h)
    · exact h
    · simpa only [neg_one_mul, neg_sub] using hNeg.mul h
  · exact Or.inl

private theorem paleyPrimeModel_adj_iff_square {q : ℕ} [Fact q.Prime]
    (hNeg : IsSquare (-1 : ZMod q)) (x y : ZMod q) :
    (paleyPrimeModel q).Adj x y ↔ x ≠ y ∧ IsSquare (x - y) := by
  change (x ≠ y ∧ ((∃ a : ZMod q, a * a = x - y) ∨ (∃ a : ZMod q, a * a = y - x))) ↔
    x ≠ y ∧ IsSquare (x - y)
  have hSquare (w : ZMod q) : (∃ a : ZMod q, a * a = w) ↔ IsSquare w := by
    simp only [isSquare_iff_exists_mul_self, eq_comm]
  rw [hSquare, hSquare, square_sub_or_iff hNeg]

private theorem prime_isSquare_neg_one {q : ℕ} [Fact q.Prime] [NeZero q]
    (hq : q % 4 = 1) : IsSquare (-1 : ZMod q) := by
  apply FiniteField.isSquare_neg_one_iff.mpr
  rw [ZMod.card, hq]
  decide

private theorem prime_ringChar_ne_two {q : ℕ} (hq : q % 4 = 1) :
    ringChar (ZMod q) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

private theorem paley_compl_iso {F : Type*} [Field F] [Fintype F]
    (hChar : ringChar F ≠ 2) {K : SimpleGraph F}
    (hAdj : ∀ x y, K.Adj x y ↔ x ≠ y ∧ IsSquare (x - y)) :
    Nonempty (Kᶜ ≃g K) := by
  classical
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hChar
  have hne : a ≠ 0 := fun h => ha (h.symm ▸ IsSquare.zero)
  let e := (Units.mk0 a hne).mulLeft
  refine ⟨⟨e, ?_⟩⟩
  intro x y
  rw [hAdj]
  change (e x ≠ e y ∧ IsSquare (e x - e y)) ↔ x ≠ y ∧ ¬ K.Adj x y
  rw [hAdj, e.injective.ne_iff]
  apply and_congr_right
  intro hxy
  change IsSquare (a * x - a * y) ↔ ¬ (x ≠ y ∧ IsSquare (x - y))
  rw [← mul_sub, and_iff_right hxy]
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hxy
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero hne hd),
    ← quadraticChar_neg_one_iff_not_isSquare, map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr ha]
  omega

/-- Multiplication by a nonsquare identifies the two Paley orientations. -/
theorem paleyPrimeModel_compl_iso {q : ℕ} [Fact q.Prime] [NeZero q]
    (hq : q % 4 = 1) : Nonempty ((paleyPrimeModel q)ᶜ ≃g paleyPrimeModel q) :=
  paley_compl_iso (prime_ringChar_ne_two hq) (paleyPrimeModel_adj_iff_square
    (prime_isSquare_neg_one hq))

private theorem paley_of_square_semilinear_subgroup {V F : Type*} [Field F] [Fintype F]
    (hChar : ringChar F ≠ 2) {K : SimpleGraph F}
    (hAdj : ∀ x y, K.Adj x y ↔ x ≠ y ∧ IsSquare (x - y))
    {H : SimpleGraph V} (hRank : HasRankThreeAutAction H)
    (hAction : HasPaleyRankThreeAction H F) : Nonempty (H ≃g K) := by
  obtain ⟨labels, P, hOrbits, hAction⟩ := hAction
  obtain ⟨d, hd⟩ := FiniteField.exists_nonsquare hChar
  have hdNe : d ≠ 0 := fun h => hd (h.symm ▸ IsSquare.zero)
  have hModel : IsRankThreeActionModel H K := by
    refine ⟨⟨1, 0, (hAdj 1 0).mpr ?_⟩, ⟨d, 0, hdNe, ?_⟩, labels, P, hOrbits, ?_⟩
    · simpa only [sub_zero] using And.intro one_ne_zero IsSquare.one
    · rw [hAdj, sub_zero]
      exact fun h => hd h.2
    intro p hp x y
    obtain ⟨a, b, σ, ha, haNe, h⟩ := hAction ⟨p, hp⟩
    change K.Adj (labels x) (labels y) ↔ K.Adj (labels (p x)) (labels (p y))
    rw [hAdj, hAdj, labels.injective.ne_iff, labels.injective.ne_iff, p.injective.ne_iff]
    rw [h x, h y, add_sub_add_right_eq_sub, ← mul_sub, ← map_sub σ]
    apply and_congr_right
    intro _
    constructor
    · intro hSquare
      exact ha.mul (hSquare.map σ)
    · intro hSquare
      have hDiv := hSquare.div ha
      rw [mul_comm, mul_div_cancel_right₀ _ haNe] at hDiv
      simpa only [σ.symm_apply_apply] using hDiv.map σ.symm
  rcases hModel.isModelUpToComplement hRank with h | h
  · exact h
  · obtain ⟨φ⟩ := h
    obtain ⟨ψ⟩ := paley_compl_iso hChar hAdj
    exact ⟨φ.trans ψ⟩

/-- The rank-three action on the prime field gives the exact Paley model. -/
theorem paleyPrimeModel_of_paleyRankThreeAction {V : Type*}
    {q : ℕ} [Fact q.Prime] [NeZero q] (hq : q % 4 = 1)
    {H : SimpleGraph V} (hRank : HasRankThreeAutAction H)
    (hAction : HasPaleyRankThreeAction H (ZMod q)) : Nonempty (H ≃g paleyPrimeModel q) :=
  paley_of_square_semilinear_subgroup (prime_ringChar_ne_two hq)
    (paleyPrimeModel_adj_iff_square (prime_isSquare_neg_one hq)) hRank hAction

/-- A graph with a rank-three subgroup acting by affine maps with square
multipliers in prime-field coordinates is the exact Paley model.
The same theorem applies to the three prime Paley rows in Table 11.8. -/
theorem paleyPrimeModel_of_square_affine_subgroup {V : Type*}
    {q : ℕ} [Fact q.Prime] [NeZero q] (hq : q % 4 = 1)
    {H : SimpleGraph V} (hRank : HasRankThreeAutAction H) (labels : V ≃ ZMod q)
    {P : Subgroup (Equiv.Perm V)} (hOrbits : HasRankThreeGraphOrbits P H)
    (hAffine : ∀ p : P, ∃ a b : ZMod q, IsSquare a ∧ a ≠ 0 ∧
      ∀ z, labels (p.val z) = a * labels z + b) : Nonempty (H ≃g paleyPrimeModel q) := by
  refine paleyPrimeModel_of_paleyRankThreeAction hq hRank ⟨labels, P, hOrbits, ?_⟩
  intro p
  obtain ⟨a, b, ha, haNe, h⟩ := hAffine p
  exact ⟨a, b, RingEquiv.refl _, ha, haNe, h⟩

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

local instance : Fact (¬ IsSquare (2 : ZMod 5)) := ⟨by
  rw [isSquare_iff_exists_mul_self]
  decide⟩

/-- The field on the exact coordinates of the Paley graph of order 25. -/
abbrev PaleyTwentyFiveField := QuadraticAlgebra (ZMod 5) 2 0

noncomputable local instance : Fintype PaleyTwentyFiveField :=
  Fintype.ofEquiv (ZMod 5 × ZMod 5) (QuadraticAlgebra.equivProd 2 0).symm

/-- The given pair-coordinate model transported to the quadratic field. -/
def paleyTwentyFiveFieldGraph : SimpleGraph PaleyTwentyFiveField :=
  pullbackGraph paleyTwentyFiveModel (QuadraticAlgebra.equivProd 2 0)

/-- The existing pair-coordinate model is the graph on the quadratic field. -/
def paleyTwentyFiveModel_fieldIso : paleyTwentyFiveModel ≃g paleyTwentyFiveFieldGraph :=
  ⟨(QuadraticAlgebra.equivProd 2 0).symm, by
    intro x y
    change paleyTwentyFiveModel.Adj
      ((QuadraticAlgebra.equivProd 2 0) ((QuadraticAlgebra.equivProd 2 0).symm x))
      ((QuadraticAlgebra.equivProd 2 0) ((QuadraticAlgebra.equivProd 2 0).symm y)) ↔
      paleyTwentyFiveModel.Adj x y
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩

private theorem paleyTwentyFive_square_coords (z : PaleyTwentyFiveField) :
    (∃ a b : ZMod 5, (a * a + 2 * b * b, 2 * a * b) = (QuadraticAlgebra.equivProd 2 0) z) ↔
    IsSquare z := by
  have hMul (a b : ZMod 5) :
      (QuadraticAlgebra.equivProd 2 0) ((⟨a, b⟩ : PaleyTwentyFiveField) * ⟨a, b⟩) =
        (a * a + 2 * b * b, 2 * a * b) := by
    change (a * a + 2 * b * b, a * b + b * a + 0 * b * b) =
      (a * a + 2 * b * b, 2 * a * b)
    apply Prod.ext
    · rfl
    · change a * b + b * a + 0 * b * b = 2 * a * b
      rw [zero_mul, zero_mul, add_zero, mul_comm b a, two_mul, add_mul]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨⟨a, b⟩, (QuadraticAlgebra.equivProd 2 0).injective ?_⟩
    exact hab.symm.trans (hMul a b).symm
  · rintro ⟨⟨a, b⟩, hab⟩
    exact ⟨a, b, (hMul a b).symm.trans (congrArg _ hab.symm)⟩

/-- Adjacency of the exact order-25 model is the nonzero square difference
relation in the quadratic field. -/
theorem paleyTwentyFiveFieldGraph_adj_iff_square (x y : PaleyTwentyFiveField) :
    paleyTwentyFiveFieldGraph.Adj x y ↔ x ≠ y ∧ IsSquare (x - y) := by
  let e := QuadraticAlgebra.equivProd (2 : ZMod 5) 0
  change (e x ≠ e y ∧ ((∃ a b : ZMod 5, (a * a + 2 * b * b, 2 * a * b) = e (x - y)) ∨
    (∃ a b : ZMod 5, (a * a + 2 * b * b, 2 * a * b) = e (y - x)))) ↔ _
  have hNeg : IsSquare (-1 : PaleyTwentyFiveField) := by
    refine ⟨⟨2, 0⟩, ?_⟩
    apply QuadraticAlgebra.ext <;> decide
  rw [e.injective.ne_iff, paleyTwentyFive_square_coords, paleyTwentyFive_square_coords,
    square_sub_or_iff hNeg]

private theorem paleyTwentyFive_ringChar_ne_two : ringChar PaleyTwentyFiveField ≠ 2 := by
  rw [← Algebra.ringChar_eq (ZMod 5) PaleyTwentyFiveField, ZMod.ringChar_zmod_n]
  decide

/-- The order-25 source row also supplies the exact pair-coordinate model
when its rank-three action is given in quadratic-field coordinates. -/
theorem paleyTwentyFiveModel_of_square_semilinear_subgroup {V : Type*}
    {H : SimpleGraph V} (hRank : HasRankThreeAutAction H)
    (hAction : HasPaleyRankThreeAction H PaleyTwentyFiveField) :
    Nonempty (H ≃g paleyTwentyFiveModel) := by
  obtain ⟨φ⟩ := paley_of_square_semilinear_subgroup paleyTwentyFive_ringChar_ne_two
    paleyTwentyFiveFieldGraph_adj_iff_square hRank hAction
  exact ⟨φ.trans paleyTwentyFiveModel_fieldIso.symm⟩

local instance : Fact (Nat.Prime 17) := ⟨by decide⟩
local instance : Fact (Nat.Prime 37) := ⟨by decide⟩
local instance : Fact (Nat.Prime 41) := ⟨by decide⟩

/-- The permutation representations of the four Paley rows of Table 11.8. -/
structure PublishedSmallPaleyActionSources : Prop where
  seventeen : ∀ (H : SimpleGraph (Fin 17)) [DecidableRel H.Adj],
    IsPrimitiveAutAction H → HasRankThreeAutAction H → H.IsSRGWith 17 8 3 4 →
    HasPaleyRankThreeAction H (ZMod 17)
  twentyFive : ∀ (H : SimpleGraph (Fin 25)) [DecidableRel H.Adj],
    IsPrimitiveAutAction H → HasRankThreeAutAction H → H.IsSRGWith 25 12 5 6 →
    HasPaleyRankThreeAction H PaleyTwentyFiveField
  thirtySeven : ∀ (H : SimpleGraph (Fin 37)) [DecidableRel H.Adj],
    IsPrimitiveAutAction H → HasRankThreeAutAction H → H.IsSRGWith 37 18 8 9 →
    HasPaleyRankThreeAction H (ZMod 37)
  fortyOne : ∀ (H : SimpleGraph (Fin 41)) [DecidableRel H.Adj],
    IsPrimitiveAutAction H → HasRankThreeAutAction H → H.IsSRGWith 41 20 9 10 →
    HasPaleyRankThreeAction H (ZMod 41)

theorem PublishedSmallPaleyActionSources.seventeen_model (sources : PublishedSmallPaleyActionSources)
    (H : SimpleGraph (Fin 17)) [DecidableRel H.Adj] (hPrim : IsPrimitiveAutAction H)
    (hRank : HasRankThreeAutAction H) (hSRG : H.IsSRGWith 17 8 3 4) :
    Nonempty (H ≃g paleyPrimeModel 17) :=
  paleyPrimeModel_of_paleyRankThreeAction (by decide) hRank (sources.seventeen H hPrim hRank hSRG)

theorem PublishedSmallPaleyActionSources.twentyFive_model (sources : PublishedSmallPaleyActionSources)
    (H : SimpleGraph (Fin 25)) [DecidableRel H.Adj] (hPrim : IsPrimitiveAutAction H)
    (hRank : HasRankThreeAutAction H) (hSRG : H.IsSRGWith 25 12 5 6) :
    Nonempty (H ≃g paleyTwentyFiveModel) :=
  paleyTwentyFiveModel_of_square_semilinear_subgroup hRank (sources.twentyFive H hPrim hRank hSRG)

theorem PublishedSmallPaleyActionSources.thirtySeven_model (sources : PublishedSmallPaleyActionSources)
    (H : SimpleGraph (Fin 37)) [DecidableRel H.Adj] (hPrim : IsPrimitiveAutAction H)
    (hRank : HasRankThreeAutAction H) (hSRG : H.IsSRGWith 37 18 8 9) :
    Nonempty (H ≃g paleyPrimeModel 37) :=
  paleyPrimeModel_of_paleyRankThreeAction (by decide) hRank (sources.thirtySeven H hPrim hRank hSRG)

theorem PublishedSmallPaleyActionSources.fortyOne_model (sources : PublishedSmallPaleyActionSources)
    (H : SimpleGraph (Fin 41)) [DecidableRel H.Adj] (hPrim : IsPrimitiveAutAction H)
    (hRank : HasRankThreeAutAction H) (hSRG : H.IsSRGWith 41 20 9 10) :
    Nonempty (H ≃g paleyPrimeModel 41) :=
  paleyPrimeModel_of_paleyRankThreeAction (by decide) hRank (sources.fortyOne H hPrim hRank hSRG)

end EPPAIII.Primitive
