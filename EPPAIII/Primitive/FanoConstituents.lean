import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fin.VecNotation

/-! # Codegree certificates for the Fano models used for G₂(2)

The correspondence between the finite models and the two G₂(2) constituents
is a published model input. This file checks both codegree obstructions.
-/

namespace EPPAIII.Primitive

open SimpleGraph

/-- The seven lines of the Fano plane, with points numbered starting at zero. -/
def fanoLines : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

private def fanoNonincidenceAdj : Sum (Fin 7) (Fin 7) → Sum (Fin 7) (Fin 7) → Prop
  | .inl p, .inr L => p ∉ fanoLines L
  | .inr L, .inl p => p ∉ fanoLines L
  | _, _ => False

/-- The Fano point-line graph with edges given by nonincidence. -/
def fanoNonincidenceGraph : SimpleGraph (Sum (Fin 7) (Fin 7)) where
  Adj := fanoNonincidenceAdj
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact id⟩

instance : DecidableRel fanoNonincidenceGraph.Adj := fun a b => by
  change Decidable (fanoNonincidenceAdj a b)
  cases a <;> cases b <;> simp only [fanoNonincidenceAdj] <;> infer_instance

/-- The incident point-line flags of the Fano plane. -/
abbrev FanoFlag := {z : Fin 7 × Fin 7 // z.1 ∈ fanoLines z.2}

private def fanoFlagAdj (a b : FanoFlag) : Prop :=
  a.val.1 ≠ b.val.1 ∧ a.val.2 ≠ b.val.2 ∧
    (a.val.1 ∈ fanoLines b.val.2 ∨ b.val.1 ∈ fanoLines a.val.2)

/-- Two flags are adjacent if their points and lines are different and at least
one point is on the other line. -/
def fanoFlagGraph : SimpleGraph FanoFlag where
  Adj := fanoFlagAdj
  symm := ⟨by rintro _ _ ⟨hp, hl, h⟩; exact ⟨hp.symm, hl.symm, h.symm⟩⟩
  loopless := ⟨by intro _ h; exact h.1 rfl⟩

instance : DecidableRel fanoFlagGraph.Adj := fun a b => by
  change Decidable (fanoFlagAdj a b)
  unfold fanoFlagAdj
  infer_instance

/-- Two points have codegree two, while an incident point and line have
codegree zero. Both pairs are distinct nonedges. -/
theorem fanoNonincidence_not_srg {n k l m : ℕ} :
    ¬ fanoNonincidenceGraph.IsSRGWith n k l m := by
  intro hs
  let p : Sum (Fin 7) (Fin 7) := .inl 0
  let q : Sum (Fin 7) (Fin 7) := .inl 1
  let L : Sum (Fin 7) (Fin 7) := .inr 0
  have hPQ : Fintype.card (fanoNonincidenceGraph.commonNeighbors p q) = 2 := by decide
  have hPL : Fintype.card (fanoNonincidenceGraph.commonNeighbors p L) = 0 := by decide
  have hOne := hs.of_not_adj (i := p) (j := q) (by decide) (by decide)
  have hTwo := hs.of_not_adj (i := p) (j := L) (by decide) (by decide)
  omega

private def flagPointOneLine123 : FanoFlag := ⟨(0, 0), by decide⟩
private def flagPointTwoLine123 : FanoFlag := ⟨(1, 0), by decide⟩
private def flagPointFourLine246 : FanoFlag := ⟨(3, 3), by decide⟩

/-- The indicated two distinct nonedges have codegrees two and four. -/
theorem fanoFlag_not_srg {n k l m : ℕ} :
    ¬ fanoFlagGraph.IsSRGWith n k l m := by
  intro hs
  let a := flagPointOneLine123
  let b := flagPointTwoLine123
  let c := flagPointFourLine246
  have hAB : Fintype.card (fanoFlagGraph.commonNeighbors a b) = 2 := by decide
  have hAC : Fintype.card (fanoFlagGraph.commonNeighbors a c) = 4 := by decide
  have hOne := hs.of_not_adj (i := a) (j := b) (by decide) (by decide)
  have hTwo := hs.of_not_adj (i := a) (j := c) (by decide) (by decide)
  omega

end EPPAIII.Primitive
