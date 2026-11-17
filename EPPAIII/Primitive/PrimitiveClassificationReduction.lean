import EPPAIII.Primitive.RankThreeContextualCoverage
import EPPAIII.Primitive.TaylorConstituentProjection

/-! # From published model recognition to primitive EPPA necessity -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.DoubleCover
open SimpleGraph

universe u v

/-- The published inputs to the smaller-pair and local recognition arguments. -/
structure PrimitiveRecognitionInputs : Prop where
  gardinerSelected : ∀ {A : Type u} [Fintype A] (G : SimpleGraph A),
    Nonempty A → IsHomogeneousGraph G → GardinerPublishedModels G
  gardinerHost : ∀ {B : Type v} [Fintype B], Nonempty B → ∀ H : SimpleGraph B,
    IsHomogeneousGraph H → GardinerPublishedModels H
  triangular : ∀ {B : Type v} [Fintype B] (H : SimpleGraph B),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
      LocallyTriangularRecognitionInputs H ∧ LocallyTriangularRecognitionInputs Hᶜ
  smallParameters : SmallRankThreeParameterCoverage.{v}
  smallModels : SmallRankThreeModelIdentification.{v}

/-- In the induction, imprimitive pairs use the separate classification.
Every primitive pair must belong to the listed primitive alternatives. -/
private def inductionCases : PairClassification.{u, v} :=
  fun G H e => primitiveCases G H e ∨ ¬ IsPrimitiveAutAction H

private theorem primitive_action_compl_iff {B : Type*} (H : SimpleGraph B) :
    IsPrimitiveAutAction H ↔ IsPrimitiveAutAction Hᶜ := by
  constructor
  · intro h R hEquiv hInv
    apply h R hEquiv
    intro q hq x y
    exact hInv q (graphAutomorphism_complement H q hq) x y
  · intro h R hEquiv hInv
    apply h R hEquiv
    intro q hq x y
    have hq' : IsGraphAutomorphism H q := by
      simpa only [compl_compl] using graphAutomorphism_complement Hᶜ q hq
    exact hInv q hq' x y

/-- The primitive necessity direction follows when the published rank-three
catalogue is covered by the proved family reductions. Its remaining inputs
are graph and group recognition, together with the specified finite results. -/
theorem primitiveCases_of_eppa_of_catalogue
    (catalog : RankThreeCatalog) (hCatalogue : RankThreeClassification.{v} catalog)
    (hFamilies : ∀ c K, K ∈ catalog c → CompleteRankThreeCase K.2)
    (hRecognize : PrimitiveRecognitionInputs.{u, v})
    (hSearch : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hFinite : PrimitiveFiniteChecks)
    {V : Type u} {W : Type v} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hPair : SmallEPPAPair G H e) (hPrim : IsPrimitiveAutAction H) :
    primitiveCases G H e := by
  classical
  by_contra hNot
  have hBad : ¬ inductionCases G H e := fun h => h.elim hNot (fun hp => hp hPrim)
  have hCompl {A : Type u} {B : Type v} (K : SimpleGraph A) (L : SimpleGraph B)
      (f : A ↪ B) : inductionCases K L f ↔ inductionCases Kᶜ Lᶜ f := by
    exact or_congr (complementClosedCases_iff orientedPrimitiveCases K L f)
      (not_congr (primitive_action_compl_iff L))
  obtain ⟨A, B, K, L, f, root, hFinA, hFinB, _, hMin, hPrimL, hRankL, _⟩ :=
    exists_oriented_primitive_rankThree_minimalCounterexample inductionCases G H e hPair hBad
      (fun _ _ _ hh _ => Or.inl (Or.inl (Or.inl hh)))
      (fun _ _ _ hi _ => Or.inr hi) hCompl
  let _ : Finite A := hFinA
  let _ : Finite B := hFinB
  let _ : Fintype B := Fintype.ofFinite B
  have hProject {X : Type u} {Y : Type v} [Finite X] [Finite Y]
      (P : SimpleGraph X) (Q : SimpleGraph Y) (j : X ↪ Y)
      (hp : SmallEPPAPair P Q j) (hc : inductionCases P Q j) : Section8ConstituentCases Q := by
    let _ : Fintype X := Fintype.ofFinite X
    let _ : Fintype Y := Fintype.ofFinite Y
    exact section8Cases_of_primitive_or_imprimitive P Q j hp hc
      (hRecognize.gardinerSelected P)
      (fun hPositive H hHom =>
        gardiner_published_implies_normalized H (hRecognize.gardinerHost hPositive H hHom))
      (homogeneousTwoGraphOrderRecognition_of_gardiner (fun R => hRecognize.gardinerSelected R))
  obtain ⟨hRec, hRecC⟩ := hRecognize.triangular L hPrimL hRankL
  have hShapes (r : A) : SelectedConstituentShapes K L f r := by
    obtain ⟨hLocal, hNonlocal⟩ := hMin.constituent_shapes hPrimL hRankL r hProject
      Or.inl hRecognize.smallParameters hRecognize.smallModels hSearch hPaley hFinite
      (fun side n hn hModel => Or.inl
        (primitiveCases_of_triangular_constituent K L f hMin.pair.eppa hMin.pair.halfOrder hRankL
          hRec hRecC hSearch hFinite (f r) side n hn hModel))
    exact ⟨hLocal, hNonlocal⟩
  have hCases := primitiveCases_of_completeRankThreeCoverage catalog hFamilies K L f
    hRankL hMin.pair.eppa hMin.pair.halfOrder (hCatalogue L hPrimL hRankL)
    hSearch hFinite root hShapes
  exact hMin.unclassified (Or.inl hCases)

/-- The primitive classification as an equivalence for the actual embedding,
with the published recognitions and finite computations explicit. -/
theorem primitiveCases_iff_eppa_of_catalogue
    (catalog : RankThreeCatalog) (hCatalogue : RankThreeClassification.{v} catalog)
    (hFamilies : ∀ c K, K ∈ catalog c → CompleteRankThreeCase K.2)
    (hRecognize : PrimitiveRecognitionInputs.{u, v})
    (hSearch : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hFinite : PrimitiveFiniteChecks)
    {V : Type u} {W : Type v} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPrim : IsPrimitiveAutAction H) :
    primitiveCases G H e ↔ IsEPPAEmbedding G H e :=
  ⟨eppa_of_primitiveCases G H e hInd hHalf hFinite,
    fun hEPPA => primitiveCases_of_eppa_of_catalogue catalog hCatalogue hFamilies
      hRecognize hSearch hPaley hFinite G H e ⟨hEPPA, hTrans, hHalf⟩ hPrim⟩

end EPPAIII.Primitive
