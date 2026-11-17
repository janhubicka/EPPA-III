import EPPAIII.Primitive.SmallConstituentSourceModels
import EPPAIII.Primitive.SmallRankThreeParameterRecognition

/-! # Relabel the printed model identities on the standard finite vertex sets -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

universe u

/-- The 20 printed model identities need only be supplied on `Fin n`. -/
def PublishedSmallRankThreeModels : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p : SRGParameters) (m : SmallConstituentHostModel) (complementModel : Bool),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentSourceModel p = some (m, complementModel) →
    Nonempty (H ≃g if complementModel then m.graphᶜ else m.graph)

/-- The published model identities on `Fin n` transport to every finite
vertex type. Both adjacency and full-action properties are preserved. -/
theorem smallRankThreeSourceModelIdentification_of_published
    (hPublished : PublishedSmallRankThreeModels) : SmallRankThreeSourceModelIdentification.{u} := by
  classical
  intro V _ H _ p m complementModel hPrim hRank hSRG hLabel
  let φ : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let K := pullbackGraph H φ
  let e : K ≃g H := ⟨φ, Iff.rfl⟩
  obtain ⟨iso⟩ := hPublished K p m complementModel (primitive_pullback_equiv H φ hPrim)
    (rankThree_pullback H φ hRank) (srg_of_iso e.symm hSRG) hLabel
  exact ⟨e.symm.trans iso⟩

end EPPAIII.Primitive
