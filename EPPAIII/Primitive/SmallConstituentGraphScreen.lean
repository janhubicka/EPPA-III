import EPPAIII.Primitive.SmallConstituentTable
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Applying the finite screen to actual SRG constituents

The parameter lookup for a bounded primitive rank-three host is an
external input. The strongly regular formulas and order bound used
to reach the lookup are proved here for actual rooted graphs.
-/

namespace EPPAIII.Primitive

open SimpleGraph

variable {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- The vertex set of the indicated rooted constituent. In the
nonadjacent case the root is excluded explicitly by graph complement. -/
abbrev constituentSet (root : V) (side : Bool) : Set V :=
  if side then Hᶜ.neighborSet root else H.neighborSet root

abbrev constituentGraph (root : V) (side : Bool) :=
  H.induce (constituentSet H root side)

/-- The vertex count and uniform neighbor count of a finite graph. -/
def HasRegularProfile {W : Type*} [Finite W] (G : SimpleGraph W)
    (q : Nat × Nat) : Prop :=
  Nat.card W = q.1 ∧ ∀ x, Nat.card (G.neighborSet x) = q.2

private theorem firstConstituent_profile (p : SRGParameters)
    (h : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (root : V) :
    HasRegularProfile (constituentGraph H root false) (p.constituentProfile false) := by
  constructor
  · change Nat.card (H.neighborSet root) = p.degree
    rw [Nat.card_eq_fintype_card, H.card_neighborSet_eq_degree]
    exact h.regular root
  · intro x
    let e : ((constituentGraph H root false).neighborSet x) ≃ H.commonNeighbors root x := {
      toFun y := ⟨y.val.val, y.val.property, y.property⟩
      invFun y := ⟨⟨y.val, y.property.1⟩, y.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    exact h.of_adj root x x.property

private theorem secondConstituent_profile [DecidableEq V] (p : SRGParameters)
    (h : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (root : V) :
    HasRegularProfile (constituentGraph H root true) (p.constituentProfile true) := by
  constructor
  · change Nat.card (Hᶜ.neighborSet root) = p.order - p.degree - 1
    rw [Nat.card_eq_fintype_card, Hᶜ.card_neighborSet_eq_degree]
    exact h.compl.regular root
  · intro x
    let eCommon : {y : H.neighborSet x // H.Adj root y} ≃ H.commonNeighbors root x := {
      toFun y := ⟨y.val.val, y.property, y.val.property⟩
      invFun y := ⟨⟨y.val, y.property.2⟩, y.property.1⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    let eOther : {y : H.neighborSet x // ¬ H.Adj root y} ≃
        (constituentGraph H root true).neighborSet x := {
      toFun y := ⟨⟨y.val.val, fun hEq => x.property.2
        (Eq.mpr (congrArg (fun t : V => H.Adj t x.val) hEq)
          (H.adj_symm y.val.property)), y.property⟩, y.val.property⟩
      invFun y := ⟨⟨y.val.val, y.property⟩, y.val.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    let e := (Equiv.sumCompl (fun y : H.neighborSet x => H.Adj root y)).symm.trans
      (Equiv.sumCongr eCommon eOther)
    have hDegree : Fintype.card (H.neighborSet x) = p.degree := by
      rw [H.card_neighborSet_eq_degree]
      exact h.regular x
    have hCommon := h.of_not_adj x.property.1 x.property.2
    have hSum := Nat.card_congr e
    rw [Nat.card_sum, Nat.card_eq_fintype_card (α := H.neighborSet x),
      Nat.card_eq_fintype_card (α := H.commonNeighbors root x), hCommon, hDegree] at hSum
    change _ = p.degree - p.nonadjacentCommon
    omega

/-- The SRG parameter formula computes both actual constituent profiles. -/
theorem constituentGraph_profile [DecidableEq V] (p : SRGParameters)
    (h : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (root : V) (side : Bool) :
    HasRegularProfile (constituentGraph H root side) (p.constituentProfile side) := by
  cases side
  · exact firstConstituent_profile H p h root
  · exact secondConstituent_profile H p h root

/-- A positive-order regular profile determines its degree as well. -/
theorem HasRegularProfile.eq_of_positive {W : Type*} [Finite W]
    {G : SimpleGraph W} {p q : Nat × Nat}
    (hp : HasRegularProfile G p) (hq : HasRegularProfile G q)
    (hpos : 0 < q.1) : p = q := by
  obtain ⟨⟨x⟩, _⟩ := Nat.card_pos_iff.mp (hq.1.symm ▸ hpos)
  exact Prod.ext (hp.1.symm.trans hq.1) ((hp.2 x).symm.trans (hq.2 x))

private theorem mu_pos_of_preconnected (p : SRGParameters)
    (h : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hConn : H.Preconnected) {a b : V} (hab : a ≠ b) (hNonadj : ¬ H.Adj a b) :
    0 < p.nonadjacentCommon := by
  by_contra hNot
  have hZero : p.nonadjacentCommon = 0 := by omega
  have hStep {u v w : V} (huv : H.Adj u v) (hvw : H.Adj v w) :
      u = w ∨ H.Adj u w := by
    by_contra! hFail
    have hCommon := h.of_not_adj hFail.1 hFail.2
    have hPos : 0 < Fintype.card (H.commonNeighbors u w) :=
      Fintype.card_pos_iff.mpr ⟨⟨v, huv, H.adj_symm hvw⟩⟩
    omega
  have hWalk {u v : V} (w : H.Walk u v) : u = v ∨ H.Adj u v := by
    induction w with
    | nil => exact Or.inl rfl
    | cons huv _ ih =>
      rcases ih with hEq | hAdj
      · exact Or.inr (hEq ▸ huv)
      · exact hStep huv hAdj
  obtain ⟨w⟩ := hConn a b
  exact (hWalk w).elim hab hNonadj

private theorem order_le_460_of_actual_profile [DecidableEq V] (p : SRGParameters)
    (h : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hConn : H.Preconnected) (hComplConn : Hᶜ.Preconnected)
    (hEdge : ∃ a b, H.Adj a b)
    (hNonedge : ∃ a b, a ≠ b ∧ ¬ H.Adj a b)
    {side : Bool} (hProfile : p.constituentProfile side ∈ smallConstituentProfiles) :
    p.order ≤ 460 := by
  obtain ⟨a, b, hab, hNonadj⟩ := hNonedge
  obtain ⟨x, y, hxy⟩ := hEdge
  have hPositive : 0 < p.order := by
    rw [← h.card]
    exact Fintype.card_pos_iff.mpr ⟨a⟩
  have hMu := mu_pos_of_preconnected H p h hConn hab hNonadj
  have hMuCompl : 0 < p.compl.nonadjacentCommon :=
    mu_pos_of_preconnected Hᶜ p.compl h.compl hComplConn (H.ne_of_adj hxy)
      (fun hAdj => hAdj.2 hxy)
  have hMuLe := H.card_commonNeighbors_le_degree_left a b
  rw [h.of_not_adj hab hNonadj, h.regular a] at hMuLe
  have hUnionLe := Finset.card_le_univ (s := H.neighborFinset a ∪ H.neighborFinset b)
  rw [h.card_neighborFinset_union_of_not_adj hab hNonadj, h.card] at hUnionLe
  apply smallConstituentHost_order_le_460 hProfile (h.param_eq _ hPositive) hMu
      (h.compl.param_eq _ hPositive) hMuCompl hMuLe
  omega

/-- Given the bounded Table 11.8 lookup for the host, its actual
constituent profile determines one of the 24 certified numerical hits.
The lookup contains no EPPA or local graph assumptions. -/
theorem smallConstituentScreen_of_srg [DecidableEq V] (p : SRGParameters)
    (h : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hConn : H.Preconnected) (hComplConn : Hᶜ.Preconnected)
    (hEdge : ∃ a b, H.Adj a b)
    (hNonedge : ∃ a b, a ≠ b ∧ ¬ H.Adj a b)
    (hCoverage : p.order ≤ 460 → p ∈ orientedSmallRankThreeTable)
    (root : V) (side : Bool) (q : Nat × Nat)
    (hProf : HasRegularProfile (constituentGraph H root side) q)
    (hSmall : q ∈ smallConstituentProfiles) :
    (p, side) ∈ smallConstituentHits := by
  have hPos : 0 < q.1 := by
    exact of_decide_eq_true
      (List.all_eq_true.mp (by decide : smallConstituentProfiles.all
        (fun p => decide (0 < p.1)) = true) _ hSmall)
  have hEq := (constituentGraph_profile H p h root side).eq_of_positive hProf hPos
  have hProfile := hEq ▸ hSmall
  exact smallConstituentHits_complete (hCoverage
    (order_le_460_of_actual_profile H p h hConn hComplConn hEdge hNonedge hProfile)) hProfile

end EPPAIII.Primitive
