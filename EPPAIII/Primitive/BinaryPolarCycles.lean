import EPPAIII.Primitive.BinaryPolarExtensions
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! # Transporting the binary five-cycle certificates into graphs -/

namespace EPPAIII.Primitive

open BlockSystems.BinaryFiveCycles
open SimpleGraph

private def cycleLabels (a b c d e : ℕ) : Fin 5 → ℕ := ![a, b, c, d, e]

private theorem cycleLabels_admissible {p : ℕ → Prop} {r : ℕ → ℕ → Prop} {a b c d e : ℕ}
    (h : IsInducedFiveCycleOn p r a b c d e) (i : Fin 5) : p (cycleLabels a b c d e i) := by
  rcases h.1 with ⟨ha, hb, hc, hd, he⟩
  fin_cases i <;> first | exact ha | exact hb | exact hc | exact hd | exact he

private theorem cycleLabels_injective {p : ℕ → Prop} {r : ℕ → ℕ → Prop}
    {a b c d e : ℕ} (h : IsInducedFiveCycleOn p r a b c d e) :
    Function.Injective (cycleLabels a b c d e) := by
  obtain ⟨hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩ := h.2.1
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [cycleLabels, eq_comm]

private def cycleEmbeddingOfCertificate {V : Type*} (G : SimpleGraph V)
    {p : ℕ → Prop} {r : ℕ → ℕ → Prop} {a b c d e : ℕ}
    (h : IsInducedFiveCycleOn p r a b c d e)
    (lift : {n // p n} → V) (hle : Function.Injective lift)
    (hrel : ∀ x y : {n // p n}, G.Adj (lift x) (lift y) ↔ r x.val y.val) :
    cycleGraph 5 ↪g G where
  toFun i := lift ⟨cycleLabels a b c d e i, cycleLabels_admissible h i⟩
  inj' := fun _ _ heq => cycleLabels_injective h (congrArg Subtype.val (hle heq))
  map_rel_iff' := by
    intro i j
    let v (i : Fin 5) := lift ⟨cycleLabels a b c d e i, cycleLabels_admissible h i⟩
    change G.Adj (v i) (v j) ↔ (cycleGraph 5).Adj i j
    obtain ⟨hab, hbc, hcd, hde, hea⟩ := h.2.2.1
    obtain ⟨hac, had, hbd, hbe, hce⟩ := h.2.2.2
    have h01 : G.Adj (v 0) (v 1) := (hrel _ _).mpr hab
    have h12 : G.Adj (v 1) (v 2) := (hrel _ _).mpr hbc
    have h23 : G.Adj (v 2) (v 3) := (hrel _ _).mpr hcd
    have h34 : G.Adj (v 3) (v 4) := (hrel _ _).mpr hde
    have h40 : G.Adj (v 4) (v 0) := (hrel _ _).mpr hea
    have h02 : ¬ G.Adj (v 0) (v 2) := (hrel _ _).not.mpr hac
    have h03 : ¬ G.Adj (v 0) (v 3) := (hrel _ _).not.mpr had
    have h13 : ¬ G.Adj (v 1) (v 3) := (hrel _ _).not.mpr hbd
    have h14 : ¬ G.Adj (v 1) (v 4) := (hrel _ _).not.mpr hbe
    have h24 : ¬ G.Adj (v 2) (v 4) := (hrel _ _).not.mpr hce
    fin_cases i <;> fin_cases j <;>
      simp [cycleGraph_adj', h01, h12, h23, h34, h40, h01.symm, h12.symm, h23.symm,
        h34.symm, h40.symm, h02, h03, h13, h14, h24, G.adj_comm (v 2) (v 0),
        G.adj_comm (v 3) (v 0), G.adj_comm (v 3) (v 1), G.adj_comm (v 4) (v 1),
        G.adj_comm (v 4) (v 2)] <;> decide

private def orthogonalSixLift (plus singular : Bool)
    (x : {n // isOrthogonalVertex plus singular n}) : OrthogonalSixVertex plus singular :=
  ⟨⟨x.val, x.property.2.1⟩, x.property⟩

private def orthogonalSixCycle (plus singular : Bool) {a b c d e : ℕ}
    (h : IsInducedFiveCycleOn (isOrthogonalVertex plus singular) (orthogonalAdj plus) a b c d e) :
    cycleGraph 5 ↪g orthogonalSixGraph plus singular :=
  cycleEmbeddingOfCertificate _ h (orthogonalSixLift plus singular)
    (fun _ _ hEq => Subtype.ext (congrArg (fun x => x.val.val) hEq))
    (fun _ _ => and_congr (not_congr ⟨fun hEq => congrArg (fun x => x.val.val) hEq,
      fun hEq => Subtype.ext (Fin.ext hEq)⟩) Iff.rfl)

private def affineOrthogonalSixCycle (plus : Bool) {a b c d e : ℕ}
    (h : IsInducedFiveCycleOn isVectorVertex (vectorAdj plus) a b c d e) :
    cycleGraph 5 ↪g vectorOrthogonalSixGraph plus :=
  cycleEmbeddingOfCertificate _ h (fun x => ⟨x.val, x.property⟩)
    (fun _ _ hEq => Subtype.ext (congrArg Fin.val hEq))
    (fun _ _ => and_congr (not_congr ⟨fun hEq => congrArg Fin.val hEq, fun hEq => Fin.ext hEq⟩) Iff.rfl)

/-- The singular and nonsingular binary reference pentagons persist
after adjoining arbitrary hyperbolic pairs. -/
def binaryOrthogonalExtended_fiveCycle (plus singular : Bool) (m : ℕ) :
    cycleGraph 5 ↪g binaryOrthogonalExtendedGraph plus singular m :=
  (orthogonalSix_into_hyperbolic_extension plus singular m).comp (match plus, singular with
    | true, true => orthogonalSixCycle true true oSixPlus_five_cycle
    | false, true => orthogonalSixCycle false true oSixMinus_five_cycle
    | true, false => orthogonalSixCycle true false noSixPlus_five_cycle
    | false, false => orthogonalSixCycle false false noSixMinus_five_cycle)

/-- The affine binary pentagons persist after adjoining hyperbolic pairs. -/
def binaryAffineOrthogonalExtended_fiveCycle (plus : Bool) (m : ℕ) :
    cycleGraph 5 ↪g binaryAffineOrthogonalExtendedGraph plus m :=
  (affineOrthogonalSix_into_hyperbolic_extension plus m).comp (match plus with
    | true => affineOrthogonalSixCycle true voSixPlus_five_cycle
    | false => affineOrthogonalSixCycle false voSixMinus_five_cycle)

private def symplecticFourLift (x : {n // isSpFourVertex n}) : BinarySymplecticFourVertex :=
  ⟨⟨x.val, x.property.2⟩, fun hEq => (Nat.ne_of_gt x.property.1) (congrArg Fin.val hEq)⟩

/-- The symplectic pentagon persists after adjoining hyperbolic pairs. -/
def binarySymplecticExtended_fiveCycle (m : ℕ) :
    cycleGraph 5 ↪g binarySymplecticExtendedGraph m :=
  (symplecticFour_into_hyperbolic_extension m).comp
    (cycleEmbeddingOfCertificate _ spFour_five_cycle symplecticFourLift
      (fun _ _ hEq => Subtype.ext (congrArg (fun x => x.val.val) hEq))
      (fun _ _ => and_congr (not_congr ⟨fun hEq => congrArg (fun x => x.val.val) hEq,
        fun hEq => Subtype.ext (Fin.ext hEq)⟩) Iff.rfl))

end EPPAIII.Primitive
