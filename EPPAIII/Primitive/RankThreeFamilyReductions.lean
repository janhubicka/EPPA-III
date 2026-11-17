import EPPAIII.Primitive.NonsingularTernaryExclusion
import EPPAIII.Primitive.OddNonsingularOrthogonal
import EPPAIII.Primitive.AffineConferenceExclusion
import EPPAIII.Primitive.AffineExceptionalScreen
import EPPAIII.Primitive.AffineFifteenThousandExclusion
import EPPAIII.Primitive.AffineSurvivorExclusions
import EPPAIII.Primitive.AffineLineSmallPaley
import EPPAIII.Primitive.AffineSemilinearExclusion
import EPPAIII.Primitive.BilinearExclusion
import EPPAIII.Primitive.BinaryAffineHalfSpinExclusion
import EPPAIII.Primitive.BinaryPolarExclusions
import EPPAIII.Primitive.BinaryUnitaryConstituents
import EPPAIII.Primitive.ConstituentShapeReduction
import EPPAIII.Primitive.ConwayConstituents
import EPPAIII.Primitive.E6Constituents
import EPPAIII.Primitive.Gewirtz
import EPPAIII.Primitive.G2ConstituentExclusions
import EPPAIII.Primitive.HalfSpinExclusion
import EPPAIII.Primitive.HigmanSims
import EPPAIII.Primitive.PolarRankThreeWitnesses
import EPPAIII.Primitive.GrassmannRookObstruction
import EPPAIII.Primitive.SporadicConstituentExclusions
import EPPAIII.Primitive.HoffmanSingleton
import EPPAIII.Primitive.UnitaryFourThreeConstituents
import EPPAIII.Primitive.TriangularConstituentReduction

/-! # Family reductions for the primitive rank-three catalogue -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers
open SimpleGraph

attribute [local instance] Classical.propDecidable

/-- Geometry and action data sufficient to use the proved family reductions.
These hypotheses concern the model alone. In particular, they do not assert
any obstruction for an EPPA selection. -/
inductive RecognizedRankThreeFamily {n : ℕ} (H : SimpleGraph (Fin n)) : Prop
  | grassmann {F V : Type} [Field F] [Finite F]
      [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (hDim : 5 ≤ Module.finrank F V)
      (hModel : IsModelUpToComplement H (grassmannGraph F V))
  | bilinear {F : Type} [Field F] {m : ℕ} (hDim : 3 ≤ m)
      (hModel : IsModelUpToComplement H (bilinearFormsGraph F m))
  | alternatingFive {q : ℕ} (hq : 2 ≤ q)
      (hSRG : let p := alternatingFiveParameters q
        H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
  | splitPolarRankThree {F : Type} [Field F] (scalars : Fin 3 ↪ F)
      (hChart : ∀ r, ∃ C : PolarSixChart (F := F) H
        (fun v => splitPolarQuadratic v = 0) splitPolarPairing,
        C.root splitPolar_root_valid = r)
  | symplecticPolarRankThree {F : Type} [Field F]
      (hChart : ∀ r, ∃ C : PolarSixChart (F := F) H
        (fun _ => True) symplecticPolarPairing, C.root trivial = r)
  | eSix {q : ℕ} (hq : 2 ≤ q)
      (hSRG : let p := eSixParameters q
        H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
      (hConnected : ∀ root, (constituentGraph H root false).Connected)
  | binaryPolar (hCharts : HasBinaryPolarConstituentCharts H)
  | binaryNonsingularUnitary (d : ℕ)
      (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms (binaryUnitaryGraph (5 + d)))
      (hModel : IsModelUpToComplement H (binaryUnitaryGraph (5 + d)))
  | oddNonsingularOrthogonal (field : OddOrthogonalField) (plus : Bool) (d : ℕ)
      (hTrans : ∀ r s, ∃ a : field.graph plus d ≃g field.graph plus d, a r = s)
      (hModel : IsModelUpToComplement H (field.graph plus d))
  | binaryAffineHalfSpin (hSRG : H.IsSRGWith 65536 2295 310 72)
  | projectiveHalfSpin {F : Type} [Field F]
      (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms (halfSpinFiveGraph F))
      (hModel : IsModelUpToComplement H (halfSpinFiveGraph F))
  | affine81Degree32 (complement : Bool)
      (hSRG : (if complement then Hᶜ else H).IsSRGWith 81 32 13 12)
  | affine169Degree72 (complement : Bool)
      (hSRG : (if complement then Hᶜ else H).IsSRGWith 169 72 31 30)
  | affine256Degree120 (complement : Bool)
      (hSRG : (if complement then Hᶜ else H).IsSRGWith 256 120 56 56)
  | affine2048Degree276 (complement : Bool)
      (hSRG : (if complement then Hᶜ else H).IsSRGWith 2048 276 44 36)
  | affine2401Degree240 (complement : Bool)
      (hSRG : (if complement then Hᶜ else H).IsSRGWith 2401 240 59 20)
  | affine2401Degree480 (complement : Bool)
      (hSRG : (if complement then Hᶜ else H).IsSRGWith 2401 480 119 90)
  | affineFifteenThousand (hSRG : H.IsSRGWith 15625 7560 3655 3660)
  | affineExceptionalProfile (i : Fin 25) (complement : Bool)
      (hSRG : let p := affineExceptionalExcludedParametersOriented i complement
        H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
  | sporadicProfile (i : Fin 13) (complement : Bool)
      (hSRG : let p := sporadicConstituentParametersOriented i complement
        H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
  | binaryProjectiveHalfSpin (hSRG : H.IsSRGWith 2295 310 85 35)
  | g2Two (hSRG : H.IsSRGWith 36 14 4 6)
  | g2Four (hSRG : H.IsSRGWith 416 100 36 20)
  | conway1408 (hSRG : H.IsSRGWith 1408 567 246 216)
  | unitaryFourThree (hSRG : H.IsSRGWith 162 56 10 24)
  | affineLine {K F : Type} [Field K] [Field F] [Fintype F] [Algebra K F]
      [FiniteDimensional K F] (KGraph : SimpleGraph F)
      (hModel : IsModelUpToComplement H KGraph)
      (hAction : HasAffineLineAction K KGraph)
      (hOrder : 8 * Module.finrank K F + 4 < Nat.card F)
  | affineSemilinear {F K V : Type} [Field F] [Field K] [Fintype F] [Fintype K]
      [Algebra F K] [FiniteDimensional F K] [Fintype V]
      [AddCommGroup V] [Module K V] [Module.Finite K V] (KGraph : SimpleGraph V)
      (hModel : IsModelUpToComplement H KGraph)
      (hq : 3 ≤ Fintype.card K) (hDim : 4 ≤ Module.finrank K V)
      (hOrigin : ∀ x : V, ∃ a : KGraph ≃g KGraph, a x = 0)
      (hAction : ∀ a : Equiv.Perm V, IsGraphAutomorphism KGraph a → a 0 = 0 →
        ∃ (g : K ≃ₐ[F] K) (f : V →ₛₗ[RingHomClass.toRingHom g] V), ∀ x, a x = f x)
  | affineConference (row : AffineConferenceRow)
      (hSRG : let p := row.parameters; H.IsSRGWith p.1 p.2.1 p.2.2.1 p.2.2.2)
      (hRank : HasRankThreeAutAction H)
      (hPoint : ∀ x, Nat.card (hostPointwiseStabilizer H {x}) ≤ row.pointBound)
  | affinePairBound {k : ℕ} (hOrder : 8 * k + 4 < n)
      (hPair : ∀ x y, x ≠ y → Nat.card (hostPointwiseStabilizer H {x, y}) ≤ k)
  | affineEightyOne (hOrder : n = 81)
      (hPair : ∀ x y, x ≠ y → Nat.card (hostPointwiseStabilizer H {x, y}) ≤ 12)
  | orthogonalSixPlus (hModel : IsModelUpToComplement H (orthogonalSixGraph true true))
  | evenTernary {a : ℕ} (ha : 1 ≤ a) (plus : Bool)
      (hHost : let p := evenTernaryParameters a plus
        H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
      (hLocal : ∀ root, let p := evenTernaryParameters a plus
        let μ := evenTernaryLocalCodegree a plus
        (constituentGraph H root false).IsSRGWith p.degree p.adjacentCommon μ μ)
  | evenTernaryOfHost {a : ℕ} (ha : 1 ≤ a) (plus : Bool)
      (hHost : let p := evenTernaryParameters a plus
        H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
  | nonsingularOrthogonalSixMinus
      (hModel : IsModelUpToComplement H (orthogonalSixGraph false false))
  | affineOrthogonalSix (plus : Bool)
      (hModel : IsModelUpToComplement H (vectorOrthogonalSixGraph plus))
  | hoffmanSingleton (hSRG : H.IsSRGWith 50 7 0 1)
  | gewirtz (hSRG : H.IsSRGWith 56 10 0 2)
      (hStabilizer : ∀ v u, v ≠ u → ¬ H.Adj v u →
        Nat.card (pointwiseGraphStabilizer H {v, u}) = 32)
  | mathieuTwentyTwo (hSRG : H.IsSRGWith 77 16 0 4) (hRank : HasRankThreeAutAction H)
      (hStabilizer : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) = 11520)
  | higmanSims (hSRG : H.IsSRGWith 100 22 0 6) {W : Type} [Fintype W]
      (M : SimpleGraph W) (hMSRG : M.IsSRGWith 77 16 0 4) (hMRank : HasRankThreeAutAction M)
      (hMStabilizer : ∀ r, Nat.card (pointwiseGraphStabilizer M {r}) = 11520)
      (hModel : ∀ r, Nonempty (nonlocalGraph H r ≃g M))
      (hStabilizer : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤ 887040)

private theorem automorphism_moving_root {V : Type*} {H : SimpleGraph V}
    (hTrans : HasTransitiveGraphAutomorphisms H) (r s : V) :
    ∃ φ : H ≃g H, φ r = s := by
  obtain ⟨p, hAdj, hRoot⟩ := hTrans r s
  exact ⟨⟨p, fun {x y} => (hAdj x y).symm⟩, hRoot⟩

/-- For a transitive split polar model one chart suffices. -/
theorem RecognizedRankThreeFamily.splitPolar_of_chart
    {n : ℕ} {H : SimpleGraph (Fin n)} {F : Type} [Field F]
    (hTrans : HasTransitiveGraphAutomorphisms H) (scalars : Fin 3 ↪ F)
    (C : PolarSixChart (F := F) H (fun v => splitPolarQuadratic v = 0) splitPolarPairing) :
    RecognizedRankThreeFamily H := by
  apply splitPolarRankThree scalars
  intro s
  obtain ⟨φ, hRoot⟩ := automorphism_moving_root hTrans (C.root splitPolar_root_valid) s
  exact ⟨C.relabel φ, by simpa only [PolarSixChart.root_relabel] using hRoot⟩

/-- For a transitive symplectic polar model one chart suffices. -/
theorem RecognizedRankThreeFamily.symplecticPolar_of_chart
    {n : ℕ} {H : SimpleGraph (Fin n)} {F : Type} [Field F]
    (hTrans : HasTransitiveGraphAutomorphisms H)
    (C : PolarSixChart (F := F) H (fun _ => True) symplecticPolarPairing) :
    RecognizedRankThreeFamily H := by
  apply symplecticPolarRankThree (F := F)
  intro s
  obtain ⟨φ, hRoot⟩ := automorphism_moving_root hTrans (C.root trivial) s
  exact ⟨C.relabel φ, by simpa only [PolarSixChart.root_relabel] using hRoot⟩

/-- The two binary constituent identities of a transitive model can be
given at one root. -/
theorem RecognizedRankThreeFamily.binaryPolar_of_root
    {n : ℕ} {H : SimpleGraph (Fin n)}
    (hTrans : HasTransitiveGraphAutomorphisms H) (r : Fin n)
    (L N : BinaryPolarConstituentChart)
    (hLocal : localGraph H r ≃g L.model.2) (hNonlocal : nonlocalGraph H r ≃g N.model.2) :
    RecognizedRankThreeFamily H := by
  apply binaryPolar
  intro s
  obtain ⟨φ, hRoot⟩ := automorphism_moving_root hTrans r s
  rw [← hRoot]
  exact ⟨⟨L, ⟨(localIso φ r).symm.trans hLocal⟩⟩,
    ⟨N, ⟨(nonlocalIso φ r).symm.trans hNonlocal⟩⟩⟩

/-- Once the E₆ parameters are known, the local connectivity input can
be supplied at one vertex. -/
theorem RecognizedRankThreeFamily.eSix_of_local_connected
    {n : ℕ} {H : SimpleGraph (Fin n)} {q : ℕ}
    (hTrans : HasTransitiveGraphAutomorphisms H) (hq : 2 ≤ q)
    (hSRG : let p := eSixParameters q
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (r : Fin n) (hConnected : (localGraph H r).Connected) : RecognizedRankThreeFamily H := by
  refine .eSix hq hSRG fun s => ?_
  change (localGraph H s).Connected
  obtain ⟨φ, hRoot⟩ := automorphism_moving_root hTrans r s
  rw [← hRoot]
  exact (localIso φ r).connected_iff.mp hConnected

/-- The published E₆ local clique-extension description at one vertex
supplies the required connectedness. -/
theorem RecognizedRankThreeFamily.eSix_of_local_model
    {n : ℕ} {H : SimpleGraph (Fin n)} {q : ℕ} {V : Type*} {J : SimpleGraph V}
    (hTrans : HasTransitiveGraphAutomorphisms H) (hq : 2 ≤ q)
    (hSRG : let p := eSixParameters q
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (r : Fin n) (hConnected : J.Connected)
    (φ : localGraph H r ≃g cliqueExtension (Fin q) J) : RecognizedRankThreeFamily H := by
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  exact eSix_of_local_connected hTrans hq hSRG r
    (φ.connected_iff.mpr (cliqueExtension_connected hConnected))

private theorem transitive_model {V W : Type*} {H : SimpleGraph V} {K : SimpleGraph W}
    (hTrans : HasTransitiveGraphAutomorphisms H) (hModel : IsModelUpToComplement H K) :
    HasTransitiveGraphAutomorphisms K := by
  rcases hModel with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact transitive_of_iso φ hTrans
  · exact transitive_of_iso (by simpa only [compl_compl] using complHostIso φ)
      (transitive_complement H hTrans)

/-- Model transitivity follows from host transitivity and the model isomorphism,
including in the complementary orientation. -/
theorem RecognizedRankThreeFamily.binaryNonsingularUnitary_of_model
    {n : ℕ} {H : SimpleGraph (Fin n)} (hTrans : HasTransitiveGraphAutomorphisms H)
    (d : ℕ) (hModel : IsModelUpToComplement H (binaryUnitaryGraph (5 + d))) :
    RecognizedRankThreeFamily H :=
  .binaryNonsingularUnitary d (transitive_model hTrans hModel) hModel

theorem RecognizedRankThreeFamily.oddNonsingularOrthogonal_of_model
    {n : ℕ} {H : SimpleGraph (Fin n)} (hTrans : HasTransitiveGraphAutomorphisms H)
    (field : OddOrthogonalField) (plus : Bool) (d : ℕ)
    (hModel : IsModelUpToComplement H (field.graph plus d)) :
    RecognizedRankThreeFamily H :=
  .oddNonsingularOrthogonal field plus d
    (automorphism_moving_root (transitive_model hTrans hModel)) hModel

theorem RecognizedRankThreeFamily.projectiveHalfSpin_of_model
    {n : ℕ} {H : SimpleGraph (Fin n)} {F : Type} [Field F]
    (hTrans : HasTransitiveGraphAutomorphisms H)
    (hModel : IsModelUpToComplement H (halfSpinFiveGraph F)) :
    RecognizedRankThreeFamily H :=
  .projectiveHalfSpin (transitive_model hTrans hModel) hModel

/-- Published model recognition of the part of the catalogue outside the
residual list. The residual predicate may specify individual rows within a
published family. -/
def RankThreeFamilyCoverage (catalog : RankThreeCatalog)
    (residual : RankThreeExternalCase → FiniteGraphModel → Prop) : Prop :=
  ∀ c K, K ∈ catalog c → RecognizedRankThreeFamily K.2 ∨ residual c K

private theorem no_constituent_form_of_exclusions {V : Type*} {G : SimpleGraph V}
    (h : (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
      (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
      (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
      (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ))) :
    ¬ HasCliqueUnionOrCoverModel G := by
  rcases h with ⟨hC, hCC, hG, hCG⟩
  rintro (⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩)
  · rcases h with h | h
    · exact (hC s t).false (Classical.choice h)
    · exact (hCC s t).false (Classical.choice h)
  · rcases h with h | h
    · exact (hG s t X Y).false (Classical.choice h)
    · exact (hCG s t X Y).false (Classical.choice h)

private theorem no_rooted_forms_of_orientation {n : ℕ} {H : SimpleGraph (Fin n)}
    (complement : Bool)
    (h : let K := if complement then Hᶜ else H
      ∀ root, ¬ HasCliqueUnionOrCoverModel (localGraph K root) ∧
        ¬ HasCliqueUnionOrCoverModel (nonlocalGraph K root)) :
    ∀ root, ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) := by
  have hModel : IsModelUpToComplement H (if complement then Hᶜ else H) := by
    cases complement
    · exact Or.inl ⟨SimpleGraph.Iso.refl⟩
    · apply Or.inr
      change Nonempty (H ≃g Hᶜᶜ)
      rw [compl_compl]
      exact ⟨SimpleGraph.Iso.refl⟩
  exact constituent_forms_exclusion_of_model h hModel

private theorem no_constituent_form_of_rook {V : Type*} {G : SimpleGraph V}
    (f : rookGraph 3 ↪g G) : ¬ HasCliqueUnionOrCoverModel G :=
  no_constituent_form_of_exclusions
    ⟨fun s t => (no_clique_union_or_compl_of_induced_rookThree f s t).1,
      fun s t => (no_clique_union_or_compl_of_induced_rookThree f s t).2,
      fun s t X Y => (no_cover_or_compl_of_induced_rookThree f s t X Y).1,
      fun s t X Y => (no_cover_or_compl_of_induced_rookThree f s t X Y).2⟩

private theorem no_rooted_forms_of_exclusions {V : Type*} {H : SimpleGraph V} (root : V)
    (h : ∀ side, let G := constituentGraph H root side
      (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
      (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
      (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
      (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ))) :
    ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) :=
  ⟨no_constituent_form_of_exclusions (h false), no_constituent_form_of_exclusions (h true)⟩

private theorem no_half_order_of_maxEppaOrder_bound {V : Type*} [Fintype V]
    {H : SimpleGraph V} {n m : ℕ} (hCard : Fintype.card V = n)
    (hBound : maxEppaOrder H ≤ m) (hStrict : 2 * m < n) : NoHalfOrderEPPA H := by
  unfold NoHalfOrderEPPA
  rw [Nat.card_eq_fintype_card, hCard]
  omega

/-- A recognized model either excludes half-order EPPA outright or
excludes all four constituent forms at every root. -/
theorem RecognizedRankThreeFamily.exclusion {n : ℕ} {H : SimpleGraph (Fin n)}
    (h : RecognizedRankThreeFamily H) (hOrthogonal : OrthogonalSearchChecks) :
    NoHalfOrderEPPA H ∨
    ∀ root, ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) := by
  cases h with
  | grassmann hDim hModel =>
      exact Or.inr (grassmann_model_excludes_forms hDim hModel)
  | bilinear hDim hModel =>
      exact Or.inr (fun root => bilinearForms_model_excludes_forms hDim root hModel)
  | alternatingFive hq hSRG =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (alternatingFive_excludes_actual_constituents H hq hSRG root))
  | splitPolarRankThree scalars hChart =>
      right
      intro root
      obtain ⟨C, hRoot⟩ := hChart root
      rw [← hRoot]
      exact ⟨no_constituent_form_of_rook (splitPolar_local_rookThree C scalars),
        no_constituent_form_of_rook (splitPolar_nonlocal_rookThree C scalars)⟩
  | symplecticPolarRankThree hChart =>
      right
      intro root
      obtain ⟨C, hRoot⟩ := hChart root
      rw [← hRoot]
      exact ⟨not_cliqueUnionOrCover_of_fiveCycle (symplecticPolar_local_pentagon C),
        not_cliqueUnionOrCover_of_fiveCycle (symplecticPolar_nonlocal_pentagon C)⟩
  | eSix hq hSRG hConnected =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (eSix_constituents_exclude_forms H hq root hSRG (hConnected root)))
  | binaryPolar hCharts => exact Or.inr (binaryPolar_constituents_exclude_forms hCharts)
  | binaryNonsingularUnitary d hTrans hModel =>
      exact Or.inr (fun root => constituent_forms_exclusion_of_model
        (binaryUnitary_constituents_exclude_forms d hTrans) hModel root)
  | oddNonsingularOrthogonal field plus d hTrans hModel =>
      right
      apply constituent_forms_exclusion_of_model _ hModel
      intro r
      obtain ⟨⟨a⟩, ⟨b⟩⟩ := field.constituentPentagons plus d hTrans r
      exact ⟨not_cliqueUnionOrCover_of_fiveCycle a, not_cliqueUnionOrCover_of_fiveCycle b⟩
  | binaryAffineHalfSpin hSRG =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (binaryAffineHalfSpin_excludes_actual_constituents H hSRG root))
  | projectiveHalfSpin hTrans hModel =>
      exact Or.inr (halfSpinFive_model_excludes_forms hTrans hModel)
  | affine81Degree32 complement hSRG =>
      exact Or.inr (no_rooted_forms_of_orientation complement fun root =>
        no_rooted_forms_of_exclusions root
          (affine_81_32_constituents_exclude_forms _ hSRG root))
  | affine169Degree72 complement hSRG =>
      exact Or.inr (no_rooted_forms_of_orientation complement fun root =>
        no_rooted_forms_of_exclusions root
          (affine_169_72_constituents_exclude_forms _ hSRG root))
  | affine256Degree120 complement hSRG =>
      exact Or.inr (no_rooted_forms_of_orientation complement fun root =>
        no_rooted_forms_of_exclusions root
          (affine_256_120_constituents_exclude_forms _ hSRG root))
  | affine2048Degree276 complement hSRG =>
      exact Or.inr (no_rooted_forms_of_orientation complement fun root =>
        no_rooted_forms_of_exclusions root
          (affine_2048_276_constituents_exclude_forms _ hSRG root))
  | affine2401Degree240 complement hSRG =>
      exact Or.inr (no_rooted_forms_of_orientation complement fun root =>
        no_rooted_forms_of_exclusions root
          (affine_2401_240_constituents_exclude_forms _ hSRG root))
  | affine2401Degree480 complement hSRG =>
      exact Or.inr (no_rooted_forms_of_orientation complement fun root =>
        no_rooted_forms_of_exclusions root
          (affine_2401_480_constituents_exclude_forms _ hSRG root))
  | affineFifteenThousand hSRG =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (affine_15625_constituents_exclude_forms H hSRG root))
  | affineExceptionalProfile i complement hSRG =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (affineExceptional_constituents_exclude_forms H i complement hSRG root))
  | sporadicProfile i complement hSRG =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (sporadic_constituents_exclude_forms H i complement hSRG root))
  | binaryProjectiveHalfSpin hSRG =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (binary_halfSpin_constituents_exclude_forms H hSRG root))
  | g2Two hSRG =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (g2Two_constituents_exclude_forms H hSRG root))
  | g2Four hSRG =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (g2Four_constituents_exclude_forms H hSRG root))
  | conway1408 hSRG =>
      exact Or.inr (conway1408_constituents_exclude_forms H hSRG)
  | unitaryFourThree hSRG =>
      exact Or.inr (unitaryFourThree_constituents_exclude_forms H hSRG)
  | affineLine KGraph hModel hAction hOrder =>
      exact Or.inl ((noHalfOrderEPPA_of_affineLine KGraph hAction hOrder).of_iso_or_compl hModel)
  | affineSemilinear KGraph hModel hq hDim hOrigin hAction =>
      left
      apply NoHalfOrderEPPA.of_iso_or_compl _ hModel
      apply (noHalfOrderEPPA_iff KGraph).mpr
      intro S hHalf heppa
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hHalf
      exact affineSemilinear_no_half_eppa _ KGraph _ heppa hHalf hq hDim hOrigin hAction
  | affineConference row hSRG hRank hPoint =>
      left
      apply (noHalfOrderEPPA_iff H).mpr
      intro S hHalf
      exact affineConference_not_eppa _ H _ row hSRG hHalf
        (fun x y z hxy hxz hStatus => hRank.2.2.2 x y x z hxy hxz hStatus) hPoint
  | affinePairBound hOrder hPair =>
      left
      apply (noHalfOrderEPPA_iff H).mpr
      intro S hHalf
      apply not_eppa_embedding_of_pair_stabilizers _ H _ hHalf _ hPair
      simpa only [Nat.card_fin] using hOrder
  | affineEightyOne hOrder hPair =>
      left
      apply (noHalfOrderEPPA_iff H).mpr
      intro S hHalf
      apply not_eppa_embedding_order_eightyOne_of_pair_stabilizers _ H _ hHalf _ hPair
      simpa only [Nat.card_fin] using hOrder
  | orthogonalSixPlus hModel =>
      exact Or.inl (hOrthogonal.oSixPlus.of_iso_or_compl hModel)
  | evenTernary ha plus hHost hLocal =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (evenTernary_constituents_exclude_forms H ha plus hHost hLocal root))
  | evenTernaryOfHost ha plus hHost =>
      exact Or.inr (fun root => no_rooted_forms_of_exclusions root
        (evenTernary_constituents_exclude_forms_of_host H ha plus hHost root))
  | nonsingularOrthogonalSixMinus hModel =>
      exact Or.inl (hOrthogonal.noSixMinus.of_iso_or_compl hModel)
  | affineOrthogonalSix plus hModel =>
      cases plus
      · exact Or.inl (hOrthogonal.voSixMinus.of_iso_or_compl hModel)
      · exact Or.inl (hOrthogonal.voSixPlus.of_iso_or_compl hModel)
  | hoffmanSingleton hSRG =>
      exact Or.inl (no_half_order_of_maxEppaOrder_bound hSRG.card
        (hoffmanSingleton_maxEppaOrder_le H hSRG) (by decide))
  | gewirtz hSRG hStabilizer =>
      exact Or.inl (no_half_order_of_maxEppaOrder_bound hSRG.card
        (gewirtz_maxEppaOrder_le H hSRG hStabilizer) (by decide))
  | mathieuTwentyTwo hSRG hRank hStabilizer =>
      exact Or.inl (no_half_order_of_maxEppaOrder_bound hSRG.card
        (mathieuTwentyTwo_maxEppaOrder_le H hSRG hRank hStabilizer) (by decide))
  | higmanSims hSRG M hMSRG hMRank hMStabilizer hModel hStabilizer =>
      exact Or.inl (no_half_order_of_maxEppaOrder_bound hSRG.card
        (higmanSims_maxEppaOrder_le_of_m22_model_of_bound H hSRG M hMSRG hMRank hMStabilizer
          hModel hStabilizer) (by decide))

/-- Remove the recognized families from the catalogue at the actual selected
embedding. The shape hypothesis concerns the same root as the catalogue
reduction and is supplied by the minimal-counterexample argument. -/
theorem primitiveCases_or_residual_rankThree_family
    {V W : Type*} [Finite V] [Finite W]
    (catalog : RankThreeCatalog) (residual : RankThreeExternalCase → FiniteGraphModel → Prop)
    (hCoverage : RankThreeFamilyCoverage catalog residual)
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hRank : HasRankThreeAutAction H) (hEppa : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (hModel : InRankThreeCatalog catalog H)
    (hOrthogonal : OrthogonalSearchChecks) (root : W)
    (hShape : HasCliqueUnionOrCoverModel (localGraph H root) ∨
      HasCliqueUnionOrCoverModel (nonlocalGraph H root)) :
    primitiveCases G H e ∨
      ∃ c : RankThreeExternalCase, ∃ model ∈ catalog c,
        residual c model ∧ IsModelUpToComplement H model.2 := by
  obtain hCases | ⟨c, model, hMem, hIso⟩ :=
    primitiveCases_or_residual_rankThree_model catalog G H e hRank hEppa hHalf hModel
      hOrthogonal root (fun _ => hShape)
  · exact Or.inl hCases
  obtain hKnown | hResidual := hCoverage c model hMem
  · obtain hExclude | hForms := hKnown.exclusion hOrthogonal
    · exact False.elim ((hExclude.of_iso_or_compl hIso).not_eppa_embedding G e hHalf hEppa)
    · obtain ⟨hLocal, hNonlocal⟩ := constituent_forms_exclusion_of_model hForms hIso root
      exact False.elim (hShape.elim hLocal hNonlocal)
  · exact Or.inr ⟨c, model, hMem, hResidual, hIso⟩

universe u v

/-- In a minimal counterexample, the smaller-pair classification supplies
the shape test. The published coverage and triangular recognition inputs
then force the host into a residual catalogue row. -/
theorem MinimalCounterexample.residual_rankThree_family
    {classified : PairClassification.{u, v}}
    {V : Type u} {W : Type v} [Finite V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel H.Adj] {e : V ↪ W}
    (h : MinimalCounterexample classified G H e)
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H) (root : V)
    (catalog : RankThreeCatalog) (residual : RankThreeExternalCase → FiniteGraphModel → Prop)
    (hClassification : RankThreeClassification.{v} catalog)
    (hCoverage : RankThreeFamilyCoverage catalog residual)
    (hProject : ∀ {A : Type u} {B : Type v} [Finite A] [Finite B]
      (K : SimpleGraph A) (L : SimpleGraph B) (f : A ↪ B),
      SmallEPPAPair K L f → classified K L f → Section8ConstituentCases L)
    (hIncludePrimitive : primitiveCases G H e → classified G H e)
    (hSmallCoverage : SmallRankThreeParameterCoverage.{v})
    (hSmallIdentify : SmallRankThreeModelIdentification.{v})
    (hSearch : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hPositive : PrimitiveFiniteChecks)
    (hRecognition : LocallyTriangularRecognitionInputs H)
    (hRecognitionCompl : LocallyTriangularRecognitionInputs Hᶜ) :
    ∃ c : RankThreeExternalCase, ∃ model ∈ catalog c,
      residual c model ∧ IsModelUpToComplement H model.2 := by
  obtain ⟨hLocal, hNonlocal⟩ := h.constituent_shapes hPrim hRank root hProject hIncludePrimitive
    hSmallCoverage hSmallIdentify hSearch hPaley hPositive
    (fun side n hn hModel => hIncludePrimitive
      (primitiveCases_of_triangular_constituent G H e h.pair.eppa h.pair.halfOrder hRank
        hRecognition hRecognitionCompl hSearch hPositive (e root) side n hn hModel))
  have hShape := (selected_subconstituent_at_least_half G H e root h.pair.transitive
    h.pair.halfOrder).imp hLocal hNonlocal
  exact (primitiveCases_or_residual_rankThree_family catalog residual hCoverage G H e hRank
    h.pair.eppa h.pair.halfOrder (hClassification H hPrim hRank) hSearch (e root)
    hShape).resolve_left (fun hCases => h.unclassified (hIncludePrimitive hCases))

end EPPAIII.Primitive
