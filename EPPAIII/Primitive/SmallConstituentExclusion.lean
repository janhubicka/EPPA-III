import EPPAIII.Primitive.FiniteExclusions
import EPPAIII.Primitive.SmallConstituentModels

/-! # Excluding the three orthogonal hosts in the small-constituent table -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

universe u

/-- The three graph models printed in bold in the small-constituent table. -/
def SmallConstituentHostModel.IsOrthogonalSearchCase (m : SmallConstituentHostModel) : Prop :=
  m = .equalBipartitionEight ∨
  m = .orthogonalSixMinus ∨
  m = .affineOrthogonalSixMinusComplement

theorem OrthogonalSearchChecks.noHalfOrder_of_smallConstituentModel
    (hSearch : OrthogonalSearchChecks) {W : Type*} [Finite W]
    (H : SimpleGraph W) (m : SmallConstituentHostModel)
    (hOrthogonal : m.IsOrthogonalSearchCase) (hIso : H ≃g m.graph) :
    NoHalfOrderEPPA H := by
  rcases hOrthogonal with hEq | hEq | hEq
  · subst m
    exact hSearch.equalBipartitionThree.of_iso hIso
  · subst m
    exact hSearch.noSixMinus.of_iso hIso
  · subst m
    exact hSearch.voSixMinus.compl.of_iso hIso

/-- A half-order EPPA witness with a screened constituent belongs to one
of the table's ordinary rows once the three orthogonal exclusions apply. -/
theorem primitiveRankThree_smallConstituent_hostModel_of_eppa
    {V : Type*} {W : Type u} [Finite V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (embedding : V ↪ W) (heppa : IsEPPAEmbedding G H embedding)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H)
    (hCoverage : SmallRankThreeParameterCoverage.{u})
    (hIdentify : SmallRankThreeModelIdentification.{u})
    (hSearch : OrthogonalSearchChecks)
    (root : W) (side : Bool) (q : Nat × Nat)
    (hProfile : HasRegularProfile (constituentGraph H root side) q)
    (hSmall : q ∈ smallConstituentProfiles) :
    ∃ p m, (p, side) ∈ smallConstituentHits ∧
      smallConstituentHostModel p = some m ∧
      Nonempty (H ≃g m.graph) ∧ ¬ m.IsOrthogonalSearchCase := by
  obtain ⟨p, m, hp, hm, ⟨hIso⟩⟩ := primitiveRankThree_smallConstituent_hostModel H
    hPrim hRank hCoverage hIdentify root side q hProfile hSmall
  refine ⟨p, m, hp, hm, ⟨hIso⟩, fun hOrthogonal => ?_⟩
  have hNo := hSearch.noHalfOrder_of_smallConstituentModel H m hOrthogonal hIso
  exact hNo.not_eppa_embedding G embedding hHalf heppa

end EPPAIII.Primitive
