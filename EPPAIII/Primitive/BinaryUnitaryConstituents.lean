import EPPAIII.Primitive.OrthogonalEightConstituents
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-! # Induced pentagons in nonsingular binary unitary graphs -/

namespace EPPAIII.Primitive

open scoped BigOperators

/-- Coefficients in `𝔽₂[ω]/(ω² + ω + 1)`, in the basis `(1,ω)`. -/
abbrev BinaryUnitaryScalar := ZMod 2 × ZMod 2

private def scalar (a : Fin 4) : BinaryUnitaryScalar := (a.val % 2, a.val / 2)

private def scalarMul (x y : BinaryUnitaryScalar) : BinaryUnitaryScalar :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1 + x.2 * y.2)

private def scalarConj : BinaryUnitaryScalar →+ BinaryUnitaryScalar where
  toFun x := (x.1 + x.2, x.2)
  map_zero' := by decide
  map_add' := by decide

private theorem scalarHermitianSwap : ∀ x y : BinaryUnitaryScalar,
    scalarConj (scalarMul x (scalarConj y)) = scalarMul y (scalarConj x) := by decide

private theorem scalarMul_zero_conj_zero : scalarMul 0 (scalarConj 0) = 0 := by decide

private def hermitian {n : ℕ} (x y : Fin n → BinaryUnitaryScalar) : BinaryUnitaryScalar :=
  ∑ i, scalarMul (x i) (scalarConj (y i))

private theorem hermitian_swap {n : ℕ} (x y : Fin n → BinaryUnitaryScalar) :
    scalarConj (hermitian x y) = hermitian y x := by
  simp only [hermitian, map_sum, scalarHermitianSwap]

private def normalRepresentative {n : ℕ} (x : Fin n → BinaryUnitaryScalar) : Prop :=
  ∃ i, x i = scalar 1 ∧ ∀ j, j < i → x j = 0

private instance {n : ℕ} (x : Fin n → BinaryUnitaryScalar) :
    Decidable (normalRepresentative x) := by
  unfold normalRepresentative
  infer_instance

/-- A nonsingular projective point in coordinates for the identity Hermitian form.
The first nonzero coordinate is normalized to `1`. -/
def BinaryUnitaryPoint (n : ℕ) :=
  {x : Fin n → BinaryUnitaryScalar // normalRepresentative x ∧ hermitian x x = scalar 1}

instance (n : ℕ) : DecidableEq (BinaryUnitaryPoint n) := by
  unfold BinaryUnitaryPoint
  infer_instance

/-- The nonorthogonality graph on the nonsingular binary unitary points. -/
def binaryUnitaryGraph (n : ℕ) : SimpleGraph (BinaryUnitaryPoint n) where
  Adj x y := x ≠ y ∧ hermitian x.val y.val ≠ 0
  symm := by
    rintro x y ⟨hne, hxy⟩
    refine ⟨hne.symm, fun hyx => hxy ?_⟩
    rw [← hermitian_swap y.val x.val, hyx, map_zero]
  loopless x h := h.1 rfl

instance (n : ℕ) : DecidableRel (binaryUnitaryGraph n).Adj := fun _ _ => by
  change Decidable (_ ∧ _)
  infer_instance

private def vertex (digits : Fin 5 → Fin 4)
    (h : normalRepresentative (scalar ∘ digits) ∧
      hermitian (scalar ∘ digits) (scalar ∘ digits) = scalar 1) : BinaryUnitaryPoint 5 :=
  ⟨scalar ∘ digits, h⟩

private def binaryUnitaryBaseRoot : BinaryUnitaryPoint 5 :=
  vertex ![1, 0, 0, 0, 0] (by decide)

private def localFive : Fin 5 → BinaryUnitaryPoint 5 :=
  ![vertex ![1, 0, 0, 1, 1] (by decide), vertex ![1, 0, 0, 1, 2] (by decide),
    vertex ![1, 0, 0, 3, 2] (by decide), vertex ![1, 0, 1, 1, 0] (by decide),
    vertex ![1, 0, 2, 0, 2] (by decide)]

private def nonlocalFive : Fin 5 → BinaryUnitaryPoint 5 :=
  ![vertex ![0, 0, 0, 0, 1] (by decide), vertex ![0, 0, 1, 1, 1] (by decide),
    vertex ![0, 0, 0, 1, 0] (by decide), vertex ![0, 1, 1, 1, 0] (by decide),
    vertex ![0, 1, 2, 0, 2] (by decide)]

private theorem localFive_mem : ∀ i, (binaryUnitaryGraph 5).Adj binaryUnitaryBaseRoot (localFive i) := by
  decide

private theorem nonlocalFive_mem :
    ∀ i, binaryUnitaryBaseRoot ≠ nonlocalFive i ∧
      ¬ (binaryUnitaryGraph 5).Adj binaryUnitaryBaseRoot (nonlocalFive i) := by
  decide

private theorem localFive_injective : Function.Injective localFive := by decide
private theorem nonlocalFive_injective : Function.Injective nonlocalFive := by decide

private theorem localFive_adj :
    ∀ i j, (binaryUnitaryGraph 5).Adj (localFive i) (localFive j) ↔
      (SimpleGraph.cycleGraph 5).Adj i j := by
  decide

private theorem nonlocalFive_adj :
    ∀ i j, (binaryUnitaryGraph 5).Adj (nonlocalFive i) (nonlocalFive j) ↔
      (SimpleGraph.cycleGraph 5).Adj i j := by
  decide

private theorem hermitian_append_zero (d : ℕ) (x y : Fin 5 → BinaryUnitaryScalar) :
    hermitian (Fin.append x (0 : Fin d → BinaryUnitaryScalar))
      (Fin.append y (0 : Fin d → BinaryUnitaryScalar)) = hermitian x y := by
  unfold hermitian
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, scalarMul_zero_conj_zero,
    Finset.sum_const_zero, add_zero]

private def zeroExtend (d : ℕ) (x : BinaryUnitaryPoint 5) : BinaryUnitaryPoint (5 + d) := by
  refine ⟨Fin.append x.val 0, ?_, ?_⟩
  · obtain ⟨i, hi, hBefore⟩ := x.property.1
    refine ⟨Fin.castAdd d i, (Fin.append_left _ _ _).trans hi, ?_⟩
    intro j hj
    have hj5 : j.val < 5 := hj.trans i.isLt
    let j' : Fin 5 := ⟨j.val, hj5⟩
    have hj' : Fin.castAdd d j' = j := Fin.ext rfl
    rw [← hj', Fin.append_left]
    exact hBefore j' hj
  · rw [hermitian_append_zero]
    exact x.property.2

private theorem zeroExtend_injective (d : ℕ) : Function.Injective (zeroExtend d) := by
  intro x y h
  apply Subtype.ext
  funext i
  have hi := congrArg (fun p : BinaryUnitaryPoint (5 + d) => p.val (Fin.castAdd d i)) h
  simpa only [zeroExtend, Fin.append_left] using hi

private def binaryUnitaryChart (d : ℕ) : binaryUnitaryGraph 5 ↪g binaryUnitaryGraph (5 + d) where
  toEmbedding := ⟨zeroExtend d, zeroExtend_injective d⟩
  map_rel_iff' := by
    intro x y
    change (zeroExtend d x ≠ zeroExtend d y ∧
      hermitian (Fin.append x.val 0) (Fin.append y.val 0) ≠ 0) ↔
      (x ≠ y ∧ hermitian x.val y.val ≠ 0)
    rw [(zeroExtend_injective d).ne_iff, hermitian_append_zero]

/-- The normalized point represented by the first coordinate vector. -/
def binaryUnitaryRoot (d : ℕ) : BinaryUnitaryPoint (5 + d) :=
  binaryUnitaryChart d binaryUnitaryBaseRoot

/-- An induced pentagon on neighbours of the coordinate root. -/
def binaryUnitaryLocalFiveCycle (d : ℕ) :
    SimpleGraph.cycleGraph 5 ↪g localGraph (binaryUnitaryGraph (5 + d)) (binaryUnitaryRoot d) where
  toEmbedding := ⟨fun i => ⟨binaryUnitaryChart d (localFive i),
    (binaryUnitaryChart d).map_rel_iff.mpr (localFive_mem i)⟩,
    fun _ _ h => localFive_injective ((binaryUnitaryChart d).injective (congrArg Subtype.val h))⟩
  map_rel_iff' := fun {i j} => (binaryUnitaryChart d).map_rel_iff.trans (localFive_adj i j)

/-- An induced pentagon on nonneighbours of the coordinate root. -/
def binaryUnitaryNonlocalFiveCycle (d : ℕ) :
    SimpleGraph.cycleGraph 5 ↪g nonlocalGraph (binaryUnitaryGraph (5 + d)) (binaryUnitaryRoot d) where
  toEmbedding := ⟨fun i => ⟨binaryUnitaryChart d (nonlocalFive i),
    (binaryUnitaryChart d).injective.ne (nonlocalFive_mem i).1,
    fun h => (nonlocalFive_mem i).2 ((binaryUnitaryChart d).map_rel_iff.mp h)⟩,
    fun _ _ h => nonlocalFive_injective ((binaryUnitaryChart d).injective (congrArg Subtype.val h))⟩
  map_rel_iff' := fun {i j} => (binaryUnitaryChart d).map_rel_iff.trans (nonlocalFive_adj i j)

/-- At any root of a transitive binary unitary graph in dimension at least
five, both constituents fail the Section 8 shape condition. -/
theorem binaryUnitary_constituents_exclude_forms (d : ℕ)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms (binaryUnitaryGraph (5 + d)))
    (root : BinaryUnitaryPoint (5 + d)) :
    ¬ HasCliqueUnionOrCoverModel (localGraph (binaryUnitaryGraph (5 + d)) root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph (binaryUnitaryGraph (5 + d)) root) := by
  let H := binaryUnitaryGraph (5 + d)
  let baseRoot := binaryUnitaryRoot d
  obtain ⟨q, hq, hRoot⟩ := hTrans baseRoot root
  have hAdj (x : BinaryUnitaryPoint (5 + d)) : H.Adj baseRoot x ↔ H.Adj root (q x) := by
    simpa only [hRoot] using hq baseRoot x
  have hNonadj (x : BinaryUnitaryPoint (5 + d)) :
      (baseRoot ≠ x ∧ ¬ H.Adj baseRoot x) ↔ (root ≠ q x ∧ ¬ H.Adj root (q x)) := by
    have hNe : baseRoot ≠ x ↔ root ≠ q x := by
      rw [← hRoot]
      exact not_congr q.injective.eq_iff.symm
    exact and_congr hNe (hAdj x).not
  let localIso : localGraph H baseRoot ≃g localGraph H root :=
    ⟨q.subtypeEquiv hAdj, fun {a b} => (hq a b).symm⟩
  let nonlocalIso : nonlocalGraph H baseRoot ≃g nonlocalGraph H root :=
    ⟨q.subtypeEquiv hNonadj, fun {a b} => (hq a b).symm⟩
  exact ⟨not_cliqueUnionOrCover_of_fiveCycle (localIso.toEmbedding.comp (binaryUnitaryLocalFiveCycle d)),
    not_cliqueUnionOrCover_of_fiveCycle (nonlocalIso.toEmbedding.comp (binaryUnitaryNonlocalFiveCycle d))⟩

end EPPAIII.Primitive
