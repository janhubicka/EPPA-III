import EPPAIII.Primitive.SmallConstituentModels
import EPPAIII.Primitive.PrimitiveCases

/-! # Identification from the printed orientation of Table 11.8

The numerical screen uses both orientations of a row, including when
its two valencies agree. The graph identification input below names
only the orientation of each representative used in the source. In
particular, the second rook-4 identity is a consequence and the
equal-valency triangular row at order 21 needs complementation.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

universe u

/-- The screened representatives in the printed orientation. The flag
indicates that the printed graph is the complement of the model's `graph`. -/
def smallConstituentSourceModel : SRGParameters → Option (SmallConstituentHostModel × Bool)
  | ⟨15, 6, 1, 3⟩ => some (.triangularComplement 6, false)
  | ⟨16, 5, 0, 2⟩ => some (.foldedFiveCube, false)
  | ⟨16, 6, 2, 2⟩ => some (.rook 4 false, false)
  | ⟨17, 8, 3, 4⟩ => some (.paleyPrime 17, false)
  | ⟨21, 10, 5, 4⟩ => some (.triangularComplement 7, true)
  | ⟨25, 8, 3, 2⟩ => some (.rook 5 false, false)
  | ⟨25, 12, 5, 6⟩ => some (.paleyTwentyFive, false)
  | ⟨27, 10, 1, 5⟩ => some (.schlaefliComplement, false)
  | ⟨28, 12, 6, 4⟩ => some (.triangularComplement 8, true)
  | ⟨35, 16, 6, 8⟩ => some (.equalBipartitionEight, false)
  | ⟨36, 10, 4, 2⟩ => some (.rook 6 false, false)
  | ⟨36, 15, 6, 6⟩ => some (.orthogonalSixMinus, false)
  | ⟨37, 18, 8, 9⟩ => some (.paleyPrime 37, false)
  | ⟨41, 20, 9, 10⟩ => some (.paleyPrime 41, false)
  | ⟨49, 12, 5, 2⟩ => some (.rook 7 false, false)
  | ⟨55, 18, 9, 4⟩ => some (.triangularComplement 11, true)
  | ⟨64, 27, 10, 12⟩ => some (.affineOrthogonalSixMinusComplement, true)
  | ⟨66, 20, 10, 4⟩ => some (.triangularComplement 12, true)
  | ⟨100, 18, 8, 2⟩ => some (.rook 10 false, false)
  | ⟨121, 20, 9, 2⟩ => some (.rook 11 false, false)
  | _ => none

/-- Every graph label in this lookup is attached to a row of the printed
parameter table, before the numerical screen adds complements. -/
theorem smallConstituentSourceModel_mem_table {p : SRGParameters}
    {m : SmallConstituentHostModel} {complementModel : Bool}
    (h : smallConstituentSourceModel p = some (m, complementModel)) :
    p ∈ smallRankThreeTable := by
  unfold smallConstituentSourceModel at h
  split at h <;> first | decide | cases h

/-- Graph identity in the printed orientation of the 20 relevant source
rows. All other oriented identities in the screen follow by transport. -/
def SmallRankThreeSourceModelIdentification : Prop :=
  ∀ {V : Type u} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (p : SRGParameters) (m : SmallConstituentHostModel) (complementModel : Bool),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentSourceModel p = some (m, complementModel) →
    Nonempty (H ≃g if complementModel then m.graphᶜ else m.graph)

private theorem smallConstituentSourceModel_of_screen {p : SRGParameters}
    {m : SmallConstituentHostModel} (h : smallConstituentHostModel p = some m) :
    smallConstituentSourceModel p = some (m, false) ∨
      smallConstituentSourceModel p.compl = some (m, true) ∨
      (m = .rook 4 true ∧ smallConstituentSourceModel p.compl = some (.rook 4 false, false)) := by
  unfold smallConstituentHostModel at h
  split at h <;> simp_all [smallConstituentSourceModel, SRGParameters.compl]

private theorem primitive_compl {V : Type*} {H : SimpleGraph V}
    (hPrimitive : IsPrimitiveAutAction H) : IsPrimitiveAutAction Hᶜ := by
  intro R hEquivalence hInvariant
  apply hPrimitive R hEquivalence
  intro a ha
  exact hInvariant a (graphAutomorphism_complement H a ha)

private theorem rankThree_compl {V : Type*} {H : SimpleGraph V}
    (hRank : HasRankThreeAutAction H) : HasRankThreeAutAction Hᶜ := by
  obtain ⟨⟨a, b, hab⟩, ⟨c, d, hcd, hncd⟩, hTransitive, hPairs⟩ := hRank
  refine ⟨⟨c, d, hcd, hncd⟩, ⟨a, b, H.ne_of_adj hab, fun h => h.2 hab⟩,
    transitive_complement H hTransitive, ?_⟩
  intro x y z w hxy hzw hAdj
  have hSame : (¬ H.Adj x y) ↔ ¬ H.Adj z w :=
    ⟨fun h => (hAdj.mp ⟨hxy, h⟩).2, fun h => (hAdj.mpr ⟨hzw, h⟩).2⟩
  obtain ⟨a, ha, hx, hy⟩ := hPairs x y z w hxy hzw (not_iff_not.mp hSame)
  exact ⟨a, graphAutomorphism_complement H a ha, hx, hy⟩

/-- The 20 source identities give the 21 oriented identities used by the
actual rooted-constituent screen. No additional graph recognition input
is needed for the opposite orientation. -/
theorem smallRankThreeModelIdentification_of_source
    (hSource : SmallRankThreeSourceModelIdentification.{u}) :
    SmallRankThreeModelIdentification.{u} := by
  intro V _ H _ p m hPrim hRank hParams hModel
  classical
  rcases smallConstituentSourceModel_of_screen hModel with hDirect | hCompl | ⟨rfl, hRook⟩
  · exact hSource H p m false hPrim hRank hParams hDirect
  · obtain ⟨iso⟩ := hSource Hᶜ p.compl m true (primitive_compl hPrim)
      (rankThree_compl hRank) hParams.compl hCompl
    exact ⟨by simpa only [Bool.true_eq, ite_true, compl_compl] using complHostIso iso⟩
  · obtain ⟨iso⟩ := hSource Hᶜ p.compl (.rook 4 false) false (primitive_compl hPrim)
      (rankThree_compl hRank) hParams.compl hRook
    change Hᶜ ≃g rookGraph 4 at iso
    refine ⟨?_⟩
    change H ≃g (rookGraph 4)ᶜ
    simpa only [compl_compl] using complHostIso iso

end EPPAIII.Primitive
