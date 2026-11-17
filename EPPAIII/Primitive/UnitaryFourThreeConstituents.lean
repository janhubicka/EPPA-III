import EPPAIII.Primitive.AlternatingFiveExclusion
import EPPAIII.Primitive.OrthogonalEightConstituents

/-! # The order-162 graph with unitary simple socle -/

namespace EPPAIII.Primitive

open SimpleGraph

private def unitaryFourThreeParameters : SRGParameters := ⟨162, 56, 10, 24⟩

/-- Both constituents of any SRG with the order-162 unitary parameters
fail all four reduced Section 8 forms on their actual vertices. -/
theorem unitaryFourThree_constituents_exclude_forms {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 162 56 10 24)
    (root : V) :
    ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
    ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) := by
  classical
  have exclude (side : Bool) : ¬ HasCliqueUnionOrCoverModel (constituentGraph H root side) := by
    let G := constituentGraph H root side
    let n := (unitaryFourThreeParameters.constituentProfile side).1
    let d := (unitaryFourThreeParameters.constituentProfile side).2
    have hProfile := constituentGraph_profile H unitaryFourThreeParameters h root side
    have hOrder : Fintype.card (constituentSet H root side) = n :=
      Nat.card_eq_fintype_card.symm.trans hProfile.1
    have hRegular : G.IsRegularOfDegree d := by
      intro x
      rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      exact hProfile.2 x
    have hExcluded := sparse_regular_constituent_excludes_forms G hRegular
      (by cases side <;> decide) (by rw [hOrder]; cases side <;> decide)
      (by rw [hOrder]; cases side <;> decide)
      (by rw [hOrder]; cases side <;> decide)
      (by rw [hOrder]; cases side <;> decide)
      (by rw [hOrder]; cases side <;> decide)
    rintro (⟨s, t, hModel⟩ | ⟨s, t, X, Y, hModel⟩)
    · rcases hModel with hIso | hCompl
      · obtain ⟨φ⟩ := hIso
        exact (hExcluded.1 s t).false φ
      · obtain ⟨φ⟩ := hCompl
        exact (hExcluded.2.1 s t).false φ
    · rcases hModel with hIso | hCompl
      · obtain ⟨φ⟩ := hIso
        exact (hExcluded.2.2.1 s t X Y).false φ
      · obtain ⟨φ⟩ := hCompl
        exact (hExcluded.2.2.2 s t X Y).false φ
  exact ⟨exclude false, exclude true⟩

end EPPAIII.Primitive
