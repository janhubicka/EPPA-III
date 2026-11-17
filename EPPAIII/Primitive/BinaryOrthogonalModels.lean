import EPPAIII.BlockSystems.BinaryFiveCycleCertificates
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Explicit binary six-dimensional models for the finite searches -/

namespace EPPAIII.Primitive

open BlockSystems.BinaryFiveCycles

/-- The standard nonzero singular or nonsingular vectors of the chosen binary form. -/
abbrev OrthogonalSixVertex (plus singular : Bool) :=
  {x : Fin 64 // isOrthogonalVertex plus singular x.val}

instance (plus singular : Bool) :
    DecidablePred (fun x : Fin 64 => isOrthogonalVertex plus singular x.val) :=
  fun x => by
    unfold isOrthogonalVertex
    infer_instance

private theorem polarPlus_comm (a b : ℕ) : polarPlus a b = polarPlus b a := by
  unfold polarPlus
  ac_rfl

private theorem polarMinus_comm (a b : ℕ) : polarMinus a b = polarMinus b a := by
  unfold polarMinus
  ac_rfl

/-- Perpendicularity graph of the specified nonzero binary six-dimensional vectors. -/
def orthogonalSixGraph (plus singular : Bool) : SimpleGraph (OrthogonalSixVertex plus singular) where
  Adj a b := a ≠ b ∧ (if plus then polarPlus a.val.val b.val.val
    else polarMinus a.val.val b.val.val) = 0
  symm := by
    constructor
    intro a b h
    rcases h with ⟨hne, hpolar⟩
    refine ⟨Ne.symm hne, ?_⟩
    simpa only [polarPlus_comm b.val.val a.val.val,
      polarMinus_comm b.val.val a.val.val] using hpolar
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Translation graph whose edges have distinct endpoints and singular difference. -/
def vectorOrthogonalSixGraph (plus : Bool) : SimpleGraph (Fin 64) where
  Adj a b := a ≠ b ∧
    (if plus then (quadPlus a + quadPlus b + polarPlus a b) % 2
     else (quadMinus a + quadMinus b + polarMinus a b) % 2) = 0
  symm := by
    constructor
    intro a b h
    rcases h with ⟨hne, hquad⟩
    refine ⟨Ne.symm hne, ?_⟩
    simpa only [polarPlus_comm b.val a.val,
      polarMinus_comm b.val a.val, Nat.add_comm (quadPlus b) (quadPlus a),
      Nat.add_comm (quadMinus b) (quadMinus a)] using hquad
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (plus singular : Bool) : DecidableRel (orthogonalSixGraph plus singular).Adj :=
  fun a b => by
    change Decidable (a ≠ b ∧
      (if plus then polarPlus a.val.val b.val.val else polarMinus a.val.val b.val.val) = 0)
    infer_instance

instance (plus : Bool) : DecidableRel (vectorOrthogonalSixGraph plus).Adj :=
  fun a b => by
    change Decidable (a ≠ b ∧
      (if plus then (quadPlus a + quadPlus b + polarPlus a b) % 2
        else (quadMinus a + quadMinus b + polarMinus a b) % 2) = 0)
    infer_instance

end EPPAIII.Primitive
