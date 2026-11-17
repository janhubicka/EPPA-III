import EPPAIII.Primitive.AlternatingFiveExclusion

/-! # Constituent profiles for the binary affine half-spin graph -/

namespace EPPAIII.Primitive

open SimpleGraph

private def binaryAffineHalfSpinParameters : SRGParameters := ⟨65536, 2295, 310, 72⟩

/-- The two actual constituents of an SRG with the binary affine half-spin
parameters violate every clique-union and generalized-cover form. -/
theorem binaryAffineHalfSpin_excludes_actual_constituents {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hSRG : H.IsSRGWith 65536 2295 310 72) (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  let G := constituentGraph H root side
  let p := binaryAffineHalfSpinParameters.constituentProfile side
  obtain ⟨hCard, hDeg⟩ := constituentGraph_profile H binaryAffineHalfSpinParameters hSRG root side
  have hOrder : Fintype.card (constituentSet H root side) = p.1 :=
    Nat.card_eq_fintype_card.symm.trans hCard
  have hRegular : G.IsRegularOfDegree p.2 := by
    intro v
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hDeg v
  apply sparse_regular_constituent_excludes_forms G hRegular
  · cases side <;> decide
  all_goals
    rw [hOrder]
    cases side <;> decide

end EPPAIII.Primitive
