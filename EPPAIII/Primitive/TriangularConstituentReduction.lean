import EPPAIII.Primitive.FiniteExclusions
import EPPAIII.Primitive.LocalKneserRecognition
import EPPAIII.Primitive.LocallyTriangularExclusions
import EPPAIII.Primitive.PrimitiveCases
import EPPAIII.Primitive.RankThree
import EPPAIII.Primitive.SmallConstituentGraphScreen

/-! # Eliminating triangular constituents in the primitive reduction -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

/-- Uniform recognition of the rooted neighbourhood graphs. -/
def UniformLocalModel {V W : Type*} (H : SimpleGraph W) (K : SimpleGraph V) : Prop :=
  ∀ r, Nonempty (localGraph H r ≃g K)

/-- Published locally triangular and locally Kneser recognition for this host.
The triangular part for widths at least five includes the model identification
of the folded cube and the point stabilizer data used by the two large
exclusions. The small Kneser lists retain the orders subsequently rejected
by the strongly regular parameter identity. -/
structure LocallyTriangularRecognitionInputs {W : Type*} [Fintype W]
    (H : SimpleGraph W) : Prop where
  triangular : ∀ m, 5 ≤ m → UniformLocalModel H (triangularModel m) →
    Nonempty (H ≃g clebschGraphᶜ) ∨
    Nonempty (H ≃g (vectorOrthogonalSixGraph true)ᶜ) ∨
    (m = 10 ∧ Fintype.card W = 256 ∧
      ∀ r, Nat.card (hostPointwiseStabilizer H {r}) ≤ 3628800) ∨
    (m = 24 ∧ Fintype.card W = 2048 ∧
      ∀ r, Nat.card (hostPointwiseStabilizer H {r}) ≤ 244823040)
  kneserFive : UniformLocalModel H (triangularModel 5)ᶜ →
    Nonempty (H ≃g (triangularModel 7)ᶜ) ∨ Fintype.card W = 63 ∨ Fintype.card W = 65
  kneserSix : UniformLocalModel H (triangularModel 6)ᶜ →
    Nonempty (H ≃g (triangularModel 8)ᶜ) ∨ Fintype.card W = 32 ∨
      Nonempty (H ≃g orthogonalSixGraph false false)
  kneserLarge : ∀ m, 7 ≤ m → UniformLocalModel H (triangularModel m)ᶜ →
    Nonempty (H ≃g (triangularModel (m + 2))ᶜ)

private theorem uniformLocalModel_of_rankThree {V W : Type*}
    {H : SimpleGraph W} {K : SimpleGraph V} (hRank : HasRankThreeAutAction H)
    (r : W) (φ : localGraph H r ≃g K) : UniformLocalModel H K := by
  intro s
  obtain ⟨q, hq, hs⟩ := hRank.2.2.1 s r
  let move : H ≃g H := ⟨q, fun {a b} => (hq a b).symm⟩
  have hMove : move s = r := hs
  have hIso : localGraph H s ≃g localGraph H r := by
    rw [← hMove]
    exact localIso move s
  exact ⟨hIso.trans φ⟩

private theorem complement_rankThree {W : Type*} {H : SimpleGraph W}
    (hRank : HasRankThreeAutAction H) : HasRankThreeAutAction Hᶜ := by
  obtain ⟨⟨a, b, hab⟩, ⟨c, d, hcd, hncd⟩, hTrans, hPairs⟩ := hRank
  refine ⟨⟨c, d, hcd, hncd⟩, ⟨a, b, hab.ne, fun h => h.2 hab⟩,
    transitive_complement H hTrans, ?_⟩
  intro u v x y huv hxy hAdj
  have hSame : (¬ H.Adj u v) ↔ ¬ H.Adj x y :=
    ⟨fun h => (hAdj.mp ⟨huv, h⟩).2, fun h => (hAdj.mpr ⟨hxy, h⟩).2⟩
  obtain ⟨q, hq, hu, hv⟩ := hPairs u v x y huv hxy (not_iff_not.mp hSame)
  exact ⟨q, graphAutomorphism_complement H q hq, hu, hv⟩

/-- A locally triangular or locally Kneser rank-three host, in width at
least five, is either a listed primitive host or has no half-order EPPA
embedding. Previously computed EPPA exclusions are explicit premises. -/
theorem listed_or_noHalfOrderEPPA_of_triangular_neighbourhood
    {W : Type*} [Fintype W] (H : SimpleGraph W) (hRank : HasRankThreeAutAction H)
    (hInputs : LocallyTriangularRecognitionInputs H) (hSearch : OrthogonalSearchChecks)
    (r : W) (m : ℕ) (hm : 5 ≤ m)
    (hLocal : IsModelUpToComplement (localGraph H r) (triangularModel m)) :
    IsListedPrimitiveHost H ∨ NoHalfOrderEPPA H := by
  classical
  rcases hLocal with hLocal | hLocal
  · obtain ⟨φ⟩ := hLocal
    have hUniform := uniformLocalModel_of_rankThree hRank r φ
    have hNonedge (x y z : W) (hxy : x ≠ y) (hxz : x ≠ z)
        (hnxy : ¬ H.Adj x y) (hnxz : ¬ H.Adj x z) :
        ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z :=
      rankThree_point_stabilizer H hRank x y z hxy hxz (iff_of_false hnxy hnxz)
    rcases hInputs.triangular m hm hUniform with hClebsch | hFolded | h256 | h2048
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr hClebsch)))))
    · exact Or.inr (hSearch.voSixPlus.compl.of_iso (Classical.choice hFolded))
    · obtain ⟨rfl, hCard, hPoint⟩ := h256
      have hBound := locallyTriangular_order256_maxEppaOrder_le H hCard hUniform hPoint hNonedge
      right
      unfold NoHalfOrderEPPA
      rw [Nat.card_eq_fintype_card, hCard]
      omega
    · obtain ⟨rfl, hCard, hPoint⟩ := h2048
      have hBound := locallyTriangular_order2048_maxEppaOrder_le H hCard hUniform hPoint hNonedge
      right
      unfold NoHalfOrderEPPA
      rw [Nat.card_eq_fintype_card, hCard]
      omega
  · obtain ⟨φ⟩ := hLocal
    have hUniform := uniformLocalModel_of_rankThree hRank r φ
    obtain ⟨k, l, μ, hSRG⟩ := rankThree_isSRG H hRank
    have listed (n : ℕ) (hn : 5 ≤ n) (hIso : Nonempty (H ≃g (triangularModel n)ᶜ)) :
        IsListedPrimitiveHost H :=
      Or.inr (Or.inl ⟨n, hn, Or.inr hIso⟩)
    by_cases h5 : m = 5
    · subst m
      exact Or.inl (listed 7 (by decide)
        (locallyComplementTriangular_five_recognition H hSRG r φ.symm
          (hInputs.kneserFive hUniform)))
    by_cases h6 : m = 6
    · subst m
      rcases locallyComplementTriangular_six_recognition H hSRG r φ.symm
          (hInputs.kneserSix hUniform) with hIso | hOrth
      · exact Or.inl (listed 8 (by decide) hIso)
      · obtain ⟨φOrth⟩ := hOrth
        exact Or.inr (hSearch.noSixMinus.of_iso φOrth)
    exact Or.inl (listed (m + 2) (by omega) (hInputs.kneserLarge m (by omega) hUniform))

/-- Triangular recognition provides the outer classification of the actual
selected EPPA pair, from either constituent and either orientation.
This supplies the `hTriangular` implication used in the Section 8 reduction. -/
theorem primitiveCases_of_triangular_constituent
    {V W : Type*} [Finite V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (hEppa : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (hRank : HasRankThreeAutAction H)
    (hInputs : LocallyTriangularRecognitionInputs H)
    (hInputsC : LocallyTriangularRecognitionInputs Hᶜ)
    (hSearch : OrthogonalSearchChecks) (hChecks : PrimitiveFiniteChecks)
    (r : W) (side : Bool) (m : ℕ) (hm : 5 ≤ m)
    (hLocal : IsModelUpToComplement (constituentGraph H r side) (triangularModel m)) :
    primitiveCases G H e := by
  cases side
  · change IsModelUpToComplement (localGraph H r) (triangularModel m) at hLocal
    rcases listed_or_noHalfOrderEPPA_of_triangular_neighbourhood H hRank hInputs hSearch
        r m hm hLocal with hListed | hNo
    · exact (primitiveCases_iff_eppa_of_listedHost G H e hEppa.1 hHalf hListed hChecks).mpr hEppa
    · exact (hNo.not_eppa_embedding G e hHalf hEppa).elim
  · change IsModelUpToComplement (nonlocalGraph H r) (triangularModel m) at hLocal
    have hLocalC : IsModelUpToComplement (localGraph Hᶜ r) (triangularModel m) := by
      rcases hLocal with hLocal | hLocal
      · obtain ⟨φ⟩ := hLocal
        exact Or.inr ⟨(localComplIso H r).trans (complHostIso φ)⟩
      · obtain ⟨φ⟩ := hLocal
        exact Or.inl ⟨by
          simpa only [compl_compl] using (localComplIso H r).trans (complHostIso φ)⟩
    have hEppaC := eppa_embedding_complement G H e hEppa
    rcases listed_or_noHalfOrderEPPA_of_triangular_neighbourhood Hᶜ
        (complement_rankThree hRank) hInputsC hSearch r m hm hLocalC with hListed | hNo
    · have hCasesC := (primitiveCases_iff_eppa_of_listedHost Gᶜ Hᶜ e
        hEppaC.1 hHalf hListed hChecks).mpr hEppaC
      exact (complementClosedCases_iff orientedPrimitiveCases G H e).mpr hCasesC
    · exact (hNo.not_eppa_embedding Gᶜ e hHalf hEppaC).elim

end EPPAIII.Primitive
