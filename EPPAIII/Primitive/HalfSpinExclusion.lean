import EPPAIII.Primitive.HalfSpinChartGeometry
import EPPAIII.Primitive.RankThreeCases

/-! # Exclusion of the projective half-spin graph -/

namespace EPPAIII.Primitive

open SimpleGraph

private def geometryRoot (F : Type*) [Field F] : HalfSpinFiveVertex F :=
  halfSpinChartIntoGeometry F (halfSpinChartOrigin F)

private def halfSpinFive_localPentagon (F : Type*) [Field F] :
    cycleGraph 5 ↪g localGraph (halfSpinFiveGraph F) (geometryRoot F) where
  toFun i := ⟨halfSpinChartIntoGeometry F ((halfSpinChart_localPentagon F i).val),
    (halfSpinChartIntoGeometry F).map_adj_iff.mpr (halfSpinChart_localPentagon F i).property⟩
  inj' := fun _ _ h => (halfSpinChart_localPentagon F).injective
    (Subtype.ext ((halfSpinChartIntoGeometry F).injective (congrArg Subtype.val h)))
  map_rel_iff' := (halfSpinChartIntoGeometry F).map_adj_iff.trans
    (halfSpinChart_localPentagon F).map_adj_iff

private def halfSpinFive_nonlocalPentagon (F : Type*) [Field F] :
    cycleGraph 5 ↪g nonlocalGraph (halfSpinFiveGraph F) (geometryRoot F) where
  toFun i := ⟨halfSpinChartIntoGeometry F ((halfSpinChart_nonlocalPentagon F i).val),
    ⟨(halfSpinChartIntoGeometry F).injective.ne (halfSpinChart_nonlocalPentagon F i).property.1,
      fun h => (halfSpinChart_nonlocalPentagon F i).property.2
        ((halfSpinChartIntoGeometry F).map_adj_iff.mp h)⟩⟩
  inj' := fun _ _ h => (halfSpinChart_nonlocalPentagon F).injective
    (Subtype.ext ((halfSpinChartIntoGeometry F).injective (congrArg Subtype.val h)))
  map_rel_iff' := (halfSpinChartIntoGeometry F).map_adj_iff.trans
    (halfSpinChart_nonlocalPentagon F).map_adj_iff

/-- Both constituents of the projective half-spin model contain an induced
pentagon, in any labelling and either host orientation. The assumed action
moves the horizontal five-space to every possible root. -/
theorem halfSpinFive_model_excludes_forms {F W : Type*} [Field F] {H : SimpleGraph W}
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms (halfSpinFiveGraph F))
    (hModel : IsModelUpToComplement H (halfSpinFiveGraph F)) (root : W) :
    ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) := by
  apply constituent_forms_exclusion_of_model _ hModel root
  intro w
  obtain ⟨q, hq, hw⟩ := hTrans (geometryRoot F) w
  let φ : halfSpinFiveGraph F ≃g halfSpinFiveGraph F :=
    { toEquiv := q, map_rel_iff' := (hq _ _).symm }
  change φ (geometryRoot F) = w at hw
  rw [← hw]
  exact ⟨not_cliqueUnionOrCover_of_fiveCycle ((SimpleGraph.Iso.toEmbedding (localIso φ _)).comp
      (halfSpinFive_localPentagon F)),
    not_cliqueUnionOrCover_of_fiveCycle ((SimpleGraph.Iso.toEmbedding (nonlocalIso φ _)).comp
      (halfSpinFive_nonlocalPentagon F))⟩

end EPPAIII.Primitive
