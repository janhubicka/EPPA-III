import EPPAIII.Primitive.SmallRankThreeParameterRecognition

/-! # Recovering the adjacent codegrees for the small rank-three table -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open SimpleGraph

/-- The published bounded table needs to specify only the order, degree,
and nonadjacent codegree of one orientation of each host. The adjacent
codegree is recovered from those data. -/
def PublishedSmallRankThreeNonadjacentCodegrees : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    IsPrimitiveAutAction H → HasRankThreeAutAction H → n ≤ 460 →
    ∃ p ∈ smallRankThreeTable, ∃ l : ℕ,
      H.IsSRGWith p.order p.degree l p.nonadjacentCommon ∨
        Hᶜ.IsSRGWith p.order p.degree l p.nonadjacentCommon

set_option maxRecDepth 8192 in
private theorem smallRankThreeTable_adjacentCommon_lt_degree :
    smallRankThreeTable.all (fun p => decide (p.adjacentCommon < p.degree)) = true := by
  decide

private theorem srg_of_table_nonadjacentCommon {V : Type*} [Fintype V]
    {H : SimpleGraph V} [DecidableRel H.Adj] {p : SRGParameters} (hp : p ∈ smallRankThreeTable)
    {l : ℕ} (h : H.IsSRGWith p.order p.degree l p.nonadjacentCommon)
    (hEdge : ∃ a b, H.Adj a b) :
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon := by
  obtain ⟨a, b, hab⟩ := hEdge
  have hPositive : 0 < p.order := h.card ▸ Fintype.card_pos_iff.mpr ⟨a⟩
  have hActual := hab.card_commonNeighbors_lt_degree
  rw [h.of_adj a b hab, h.regular a] at hActual
  have hTable := of_decide_eq_true
    (List.all_eq_true.mp smallRankThreeTable_adjacentCommon_lt_degree p hp)
  have hEquation : p.ParameterEquation :=
    (of_decide_eq_true (List.all_eq_true.mp smallRankThreeTable_valid p hp)).2.2
  have hPositiveDegree : 0 < p.degree := Nat.zero_lt_of_lt hActual
  have hSubtraction := Nat.mul_left_cancel hPositiveDegree
    ((h.param_eq H hPositive).trans hEquation.symm)
  have hAdjacentCommon : l = p.adjacentCommon := by omega
  exact hAdjacentCommon ▸ h

/-- Recover the actual adjacent codegree from the three checked columns
of any printed row. The adjacent codegree itself remains a kernel-checked
consequence even when that column contains a typographical error. -/
theorem publishedSmallRankThreeTable_of_nonadjacentCodegrees
    (hSource : PublishedSmallRankThreeNonadjacentCodegrees) : PublishedSmallRankThreeTable := by
  intro n H _ hPrim hRank hBound
  obtain ⟨p, hp, l, hRow | hRow⟩ := hSource H hPrim hRank hBound
  · exact ⟨p, hp, Or.inl (srg_of_table_nonadjacentCommon hp hRow hRank.1)⟩
  · obtain ⟨a, b, hab, hNonadj⟩ := hRank.2.1
    exact ⟨p, hp, Or.inr (srg_of_table_nonadjacentCommon hp hRow ⟨a, b, hab, hNonadj⟩)⟩

end EPPAIII.Primitive
