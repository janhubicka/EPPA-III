import EPPAIII.Primitive.SmallConstituentExclusion
import EPPAIII.Primitive.RookBounds
import Mathlib.Data.Fin.VecNotation

/-! # Discharging the screened small-constituent cases -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

universe u

private instance : DecidableRel foldedFiveCubeModel.Adj :=
  fun a b => by
    change Decidable (a ≠ b ∧ (a.val ^^^ b.val) ∈ ([1, 2, 4, 8, 15] : List ℕ))
    infer_instance

/-- The folded cube in the numerical screen has the certificate labels. -/
theorem foldedFiveCube_eq_clebsch : foldedFiveCubeModel = clebschGraph := by
  have h : ∀ a b : Fin 16, foldedFiveCubeModel.Adj a b ↔ clebschGraph.Adj a b := by
    decide
  exact SimpleGraph.ext (funext fun a => funext fun b => propext (h a b))

private def schlafliPairLabels : Fin 15 → TwoSet (Fin 6) :=
  ![⟨{0, 1}, by decide⟩, ⟨{0, 2}, by decide⟩, ⟨{0, 3}, by decide⟩,
    ⟨{0, 4}, by decide⟩, ⟨{0, 5}, by decide⟩, ⟨{1, 2}, by decide⟩,
    ⟨{1, 3}, by decide⟩, ⟨{1, 4}, by decide⟩, ⟨{1, 5}, by decide⟩,
    ⟨{2, 3}, by decide⟩, ⟨{2, 4}, by decide⟩, ⟨{2, 5}, by decide⟩,
    ⟨{3, 4}, by decide⟩, ⟨{3, 5}, by decide⟩, ⟨{4, 5}, by decide⟩]

private def schlafliLabel (a : Fin 27) : SchlaefliVertex :=
  if h : a.val < 12 then
    .inl (decide (6 ≤ a.val), ⟨a.val % 6, by omega⟩)
  else
    .inr (schlafliPairLabels ⟨a.val - 12, by omega⟩)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem schlafliLabel_bijective : Function.Bijective schlafliLabel := by
  decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
/-- Identify the two sixes and the lexicographic pairs in the certificate
labelling of the Schläfli graph. -/
noncomputable def schlaefliModelIso : schlaefliModel ≃g schlafliGraph := by
  have h : ∀ a b : Fin 27, schlaefliModel.Adj (schlafliLabel a) (schlafliLabel b) ↔
      schlafliGraph.Adj a b := by
    decide
  exact (show schlafliGraph ≃g schlaefliModel from
    ⟨Equiv.ofBijective schlafliLabel schlafliLabel_bijective, fun {a b} => h a b⟩).symm

private def validScreenLabel : SmallConstituentHostModel → Bool
  | .rook n _ => decide (3 ≤ n)
  | .triangularComplement n => decide (5 ≤ n)
  | .paleyPrime q => decide (q ∈ ([17, 37, 41] : List ℕ))
  | _ => true

private theorem validScreenLabel_of_hit {p : SRGParameters} {side : Bool}
    {m : SmallConstituentHostModel} (hHit : (p, side) ∈ smallConstituentHits)
    (hModel : smallConstituentHostModel p = some m) : validScreenLabel m = true := by
  have h : smallConstituentHits.all
      (fun (p, _) => ((smallConstituentHostModel p).map validScreenLabel).getD false) = true :=
    by decide
  have hh := List.all_eq_true.mp h (p, side) hHit
  simpa only [hModel, Option.map_some, Option.getD_some] using hh

/-- The four Paley hosts appearing in the small-constituent screen. -/
structure SmallPaleyExclusions : Prop where
  prime : ∀ q ∈ ([17, 37, 41] : List ℕ), NoHalfOrderEPPA (paleyPrimeModel q)
  twentyFive : NoHalfOrderEPPA paleyTwentyFiveModel

/-- A screened small constituent yields one of the primitive alternatives
for the actual selected embedding. Apart from the published catalogue's
coverage and identities this uses the finite searches and the four
specified Paley exclusions. -/
theorem primitiveCases_of_screened_small_constituent
    {V : Type*} {W : Type u} [Finite V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (hEPPA : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H)
    (hCoverage : SmallRankThreeParameterCoverage.{u})
    (hIdentify : SmallRankThreeModelIdentification.{u})
    (hSearch : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hPositive : PrimitiveFiniteChecks)
    (root : W) (side : Bool) (q : ℕ × ℕ)
    (hProfile : HasRegularProfile (constituentGraph H root side) q)
    (hSmall : q ∈ smallConstituentProfiles) :
    primitiveCases G H e := by
  obtain ⟨p, m, hHit, hModel, ⟨φ⟩⟩ := primitiveRankThree_smallConstituent_hostModel
    H hPrim hRank hCoverage hIdentify root side q hProfile hSmall
  have hValid := validScreenLabel_of_hit hHit hModel
  have listed (h : IsListedPrimitiveHost H) : primitiveCases G H e :=
    (primitiveCases_iff_eppa_of_listedHost G H e hEPPA.1 hHalf h hPositive).mpr hEPPA
  have exclude (h : NoHalfOrderEPPA H) : primitiveCases G H e :=
    (h.not_eppa_embedding G e hHalf hEPPA).elim
  cases m with
  | rook n c =>
      have hn : 3 ≤ n := of_decide_eq_true hValid
      cases c
      · exact primitiveCases_of_rook_model G H e hEPPA hHalf n hn (Or.inl ⟨φ⟩)
      · exact primitiveCases_of_rook_model G H e hEPPA hHalf n hn (Or.inr ⟨φ⟩)
  | triangularComplement n =>
      exact listed (Or.inr (Or.inl ⟨n, of_decide_eq_true hValid, Or.inr ⟨φ⟩⟩))
  | paleyPrime n =>
      exact exclude ((hPaley.prime n (of_decide_eq_true hValid)).of_iso φ)
  | paleyTwentyFive =>
      exact exclude (hPaley.twentyFive.of_iso φ)
  | foldedFiveCube =>
      have ψ : H ≃g clebschGraph := by
        simpa only [SmallConstituentHostModel.graph, foldedFiveCube_eq_clebsch] using φ
      exact listed (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨ψ⟩)))))
  | schlaefliComplement =>
      exact listed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨φ.trans (complHostIso schlaefliModelIso)⟩)))))
  | equalBipartitionEight =>
      exact exclude (hSearch.equalBipartitionThree.of_iso φ)
  | orthogonalSixMinus =>
      exact exclude (hSearch.noSixMinus.of_iso φ)
  | affineOrthogonalSixMinusComplement =>
      exact exclude (hSearch.voSixMinus.compl.of_iso φ)

end EPPAIII.Primitive
