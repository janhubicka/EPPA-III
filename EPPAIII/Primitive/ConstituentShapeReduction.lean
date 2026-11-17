import EPPAIII.Primitive.MinimalCounterexample
import EPPAIII.Primitive.OrthogonalEightConstituents
import EPPAIII.Primitive.SmallConstituentCases

/-! # From smaller classified pairs to the Section 8 constituent shapes

A selected half-order constituent inherits EPPA and is classified by
minimality. Its host is a clique-union or cover model once the small
regular profiles and triangular models are excluded. The small-profile
elimination uses the checked finite screen in both host orientations.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers
open EPPAIII.DoubleCover

universe u v

/-- One of the regular constituent profiles appearing in the finite screen,
in either orientation. -/
def HasScreenedSmallProfile {W : Type*} [Finite W] (H : SimpleGraph W) : Prop :=
  ∃ p ∈ smallConstituentProfiles, HasRegularProfile H p ∨ HasRegularProfile Hᶜ p

/-- Host-level information used from the classification of a smaller
selected pair. The triangular and finite exceptions are kept explicit. -/
def Section8ConstituentCases {W : Type*} [Finite W] (H : SimpleGraph W) : Prop :=
  HasCliqueUnionOrCoverModel H ∨
  (∃ n ≥ 5, IsModelUpToComplement H (triangularModel n)) ∨
  HasScreenedSmallProfile H

theorem HasRegularProfile.of_iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {p : ℕ × ℕ}
    (h : HasRegularProfile H p) (φ : G ≃g H) : HasRegularProfile G p :=
  ⟨(Nat.card_congr φ.toEquiv).trans h.1,
    fun x => (Nat.card_congr (φ.mapNeighborSet x)).trans (h.2 (φ x))⟩

/-- The half-order EPPA pair with a screened constituent is already a
primitive classification case, regardless of the constituent orientation. -/
theorem primitiveCases_of_screened_constituent_up_to_compl
    {V : Type u} {W : Type v} [Finite V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (hEPPA : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H)
    (hCoverage : SmallRankThreeParameterCoverage.{v})
    (hIdentify : SmallRankThreeModelIdentification.{v})
    (hSearch : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hPositive : PrimitiveFiniteChecks)
    (root : W) (side : Bool)
    (hSmall : HasScreenedSmallProfile (constituentGraph H root side)) :
    primitiveCases G H e := by
  classical
  obtain ⟨q, hq, hProfile | hProfile⟩ := hSmall
  · exact primitiveCases_of_screened_small_constituent
      G H e hEPPA hHalf hPrim hRank hCoverage hIdentify hSearch hPaley hPositive
      root side q hProfile hq
  have hPrimC : IsPrimitiveAutAction Hᶜ := by
    intro R hEquiv hInvariant
    apply hPrim R hEquiv
    intro a ha
    exact hInvariant a (graphAutomorphism_complement H a ha)
  have hRankC : HasRankThreeAutAction Hᶜ := by
    obtain ⟨⟨a, b, hab⟩, ⟨c, d, hcd, hncd⟩, hTrans, hPairs⟩ := hRank
    refine ⟨⟨c, d, hcd, hncd⟩, ⟨a, b, H.ne_of_adj hab, fun h => h.2 hab⟩,
      transitive_complement H hTrans, ?_⟩
    intro x y z w hxy hzw hAdj
    have hSame : (¬ H.Adj x y) ↔ ¬ H.Adj z w :=
      ⟨fun h => (hAdj.mp ⟨hxy, h⟩).2, fun h => (hAdj.mpr ⟨hzw, h⟩).2⟩
    obtain ⟨a, ha, hx, hy⟩ := hPairs x y z w hxy hzw (not_iff_not.mp hSame)
    exact ⟨a, graphAutomorphism_complement H a ha, hx, hy⟩
  have hProfileC : HasRegularProfile (constituentGraph Hᶜ root (!side)) q := by
    cases side
    · exact hProfile.of_iso (nonlocalComplIso H root)
    · exact hProfile.of_iso (localComplIso H root)
  exact (complementClosedCases_iff orientedPrimitiveCases G H e).mpr
    (primitiveCases_of_screened_small_constituent Gᶜ Hᶜ e
      (eppa_embedding_complement G H e hEPPA) hHalf hPrimC hRankC hCoverage hIdentify
      hSearch hPaley hPositive root (!side) q hProfileC hq)

/-- At a selected root of a minimal counterexample, each sufficiently
large selected constituent has the asserted host form. The smaller-pair
classification supplies the three possible kinds of hosts. The remaining
triangular-recognition input classifies a counterexample host whenever
one of its constituents is triangular up to complement. -/
theorem MinimalCounterexample.constituent_shapes
    {classified : PairClassification.{u, v}}
    {V : Type u} {W : Type v} [Finite V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel H.Adj] {e : V ↪ W}
    (h : MinimalCounterexample classified G H e) (hPrim : IsPrimitiveAutAction H)
    (hRank : HasRankThreeAutAction H) (root : V)
    (hProject : ∀ {A : Type u} {B : Type v} [Finite A] [Finite B]
      (K : SimpleGraph A) (L : SimpleGraph B) (f : A ↪ B),
      SmallEPPAPair K L f → classified K L f → Section8ConstituentCases L)
    (hIncludePrimitive : primitiveCases G H e → classified G H e)
    (hCoverage : SmallRankThreeParameterCoverage.{v})
    (hIdentify : SmallRankThreeModelIdentification.{v})
    (hSearch : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hPositive : PrimitiveFiniteChecks)
    (hTriangular : ∀ side (n : ℕ), 5 ≤ n →
      IsModelUpToComplement (constituentGraph H (e root) side) (triangularModel n) →
        classified G H e) :
    (Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) →
      HasCliqueUnionOrCoverModel (localGraph H (e root))) ∧
    (Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root))) := by
  obtain ⟨hLocal, hNonlocal⟩ := h.classified_subconstituents hRank root
  have shape (side : Bool) (hc : Section8ConstituentCases
      (constituentGraph H (e root) side)) :
      HasCliqueUnionOrCoverModel (constituentGraph H (e root) side) := by
    rcases hc with hc | ⟨n, hn, ht⟩ | hs
    · exact hc
    · exact (h.unclassified (hTriangular side n hn ht)).elim
    · exact (h.unclassified (hIncludePrimitive
        (primitiveCases_of_screened_constituent_up_to_compl
          G H e h.pair.eppa h.pair.halfOrder hPrim hRank hCoverage hIdentify
          hSearch hPaley hPositive (e root) side hs))).elim
  exact ⟨fun hs => shape false (hProject _ _ _
      ⟨local_eppa G H e h.pair.eppa root, localGraph_transitive H hRank (e root), hs⟩ (hLocal hs)),
    fun hs => shape true (hProject _ _ _
      ⟨nonlocal_eppa G H e h.pair.eppa root, nonlocalGraph_transitive H hRank (e root), hs⟩
      (hNonlocal hs))⟩

end EPPAIII.Primitive
