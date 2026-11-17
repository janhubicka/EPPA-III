import EPPAIII.BlockSystems.UnequalCase2Triangle
import EPPAIII.Primitive.RankThree
import EPPAIII.Primitive.SmallConstituentTable
import EPPAIII.Primitive.StronglyRegularCovers
import Mathlib.Data.Fintype.EquivFin

/-! # From a published Table 11.8 row to the oriented parameters of the host -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open SimpleGraph

universe u

/-- The graph-level output of the bounded part of Table 11.8. On each
standard vertex set the source supplies one row, in either of the two
complementary orientations. In particular, equal-degree complements
need not both occur among the printed rows. -/
def PublishedSmallRankThreeTable : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    IsPrimitiveAutAction H → HasRankThreeAutAction H → n ≤ 460 →
    ∃ p ∈ smallRankThreeTable,
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon ∨
        Hᶜ.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon

/-- The oriented parameter coverage used by the constituent screen. -/
def SmallRankThreeParameterCoverage : Prop :=
  ∀ {V : Type u} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (p : SRGParameters),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    p.order ≤ 460 → p ∈ orientedSmallRankThreeTable

/-- The order, valency and both codegrees are determined on an actual
rank-three graph, since both off-diagonal orbits are nonempty. -/
theorem srg_parameters_unique_of_rankThree {V : Type*} [Fintype V]
    {H : SimpleGraph V} [DecidableRel H.Adj] (hRank : HasRankThreeAutAction H)
    {p q : SRGParameters}
    (hp : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hq : H.IsSRGWith q.order q.degree q.adjacentCommon q.nonadjacentCommon) : p = q := by
  obtain ⟨a, b, hab⟩ := hRank.1
  obtain ⟨c, d, hcd, hNonadj⟩ := hRank.2.1
  have hOrder := hp.card.symm.trans hq.card
  have hDegree := (hp.regular a).symm.trans (hq.regular a)
  have hAdjacent := (hp.of_adj a b hab).symm.trans (hq.of_adj a b hab)
  have hNonadjacent := (hp.of_not_adj hcd hNonadj).symm.trans (hq.of_not_adj hcd hNonadj)
  cases p
  cases q
  simp_all

/-- The full rank-three action transports to any equivalent vertex type. -/
theorem rankThree_pullback {V W : Type*} (H : SimpleGraph W) (φ : V ≃ W)
    (hRank : HasRankThreeAutAction H) : HasRankThreeAutAction (pullbackGraph H φ) := by
  obtain ⟨a, b, hab⟩ := hRank.1
  obtain ⟨c, d, hcd, hNonadj⟩ := hRank.2.1
  have hBack : pullbackGraph (pullbackGraph H φ) φ.symm = H := by
    ext u v
    change H.Adj (φ (φ.symm u)) (φ (φ.symm v)) ↔ H.Adj u v
    rw [φ.apply_symm_apply, φ.apply_symm_apply]
  refine ⟨⟨φ.symm a, φ.symm b, ?_⟩, ⟨φ.symm c, φ.symm d, φ.symm.injective.ne hcd, ?_⟩,
    vertex_transitive_pullback H φ hRank.2.2.1,
    pair_orbits_of_pullback (pullbackGraph H φ) φ.symm (hBack.symm ▸ hRank.2.2.2)⟩
  · simpa only [pullbackGraph, φ.apply_symm_apply] using hab
  · simpa only [pullbackGraph, φ.apply_symm_apply] using hNonadj

/-- Relabel an actual finite host on the standard vertex set and read
one row of the published table. Complementation and uniqueness of the
SRG parameters give the orientation of the original host. -/
theorem smallRankThreeParameterCoverage_of_publishedTable (hTable : PublishedSmallRankThreeTable) :
    SmallRankThreeParameterCoverage.{u} := by
  classical
  intro V _ H _ p hPrim hRank hSRG hBound
  let φ : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let K := pullbackGraph H φ
  let e : K ≃g H := ⟨φ, Iff.rfl⟩
  have hKRank : HasRankThreeAutAction K := rankThree_pullback H φ hRank
  have hKSRG : K.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon :=
    srg_of_iso e.symm hSRG
  obtain ⟨q, hq, hK | hK⟩ :=
    hTable K (primitive_pullback_equiv H φ hPrim) hKRank (hSRG.card.trans_le hBound)
  · have hEq := srg_parameters_unique_of_rankThree hKRank hKSRG hK
    exact List.mem_flatMap.mpr ⟨q, hq, by simp [hEq]⟩
  · have hKCompl : K.IsSRGWith q.compl.order q.compl.degree q.compl.adjacentCommon
        q.compl.nonadjacentCommon := srg_of_eq (compl_compl K) hK.compl
    have hEq := srg_parameters_unique_of_rankThree hKRank hKSRG hKCompl
    exact List.mem_flatMap.mpr ⟨q, hq, by simp [hEq]⟩

end EPPAIII.Primitive
