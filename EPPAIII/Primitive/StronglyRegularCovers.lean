import EPPAIII.CliqueCovers.Basic
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import EPPAIII.BlockSystems.TransitiveClusterHomogeneity
import EPPAIII.BlockSystems.TransitiveSeparatedHalf
import EPPAIII.CliqueCovers.CoverVertexTransitivity
import EPPAIII.DoubleCover.HomogeneityComplement
import EPPAIII.EPPA.HostRelabel
import EPPAIII.EPPA.BaseRelabel

/-! # Common-neighbour obstructions for strongly regular clique covers -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- One nonedge without a common neighbour forces every connected component
of a strongly regular graph to be complete. -/
theorem srg_cluster_of_empty_common_nonedge {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k l m : ℕ}
    (hSRG : G.IsSRGWith n k l m) {a b : V} (hab : a ≠ b)
    (hna : ¬G.Adj a b) (hEmpty : ∀ z, ¬(G.Adj a z ∧ G.Adj b z)) :
    ∀ x y z, G.Adj x y → G.Adj y z → x ≠ z → G.Adj x z := by
  classical
  have : IsEmpty (G.commonNeighbors a b) := ⟨fun w => hEmpty w.val w.property⟩
  have hZero : m = 0 := (hSRG.of_not_adj hab hna).symm.trans Fintype.card_of_isEmpty
  intro x y z hxy hyz hxz
  by_contra hNot
  have hPos : 0 < Fintype.card (G.commonNeighbors x z) :=
    Fintype.card_pos_iff.mpr ⟨⟨y, hxy, hyz.symm⟩⟩
  rw [hSRG.of_not_adj hxz hNot, hZero] at hPos
  exact (Nat.lt_irrefl 0) hPos

/-- A strongly regular graph cannot have one edge with a common neighbour
and another edge without one. -/
theorem srg_false_of_mixed_triangle_edges {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k l m : ℕ}
    (hSRG : G.IsSRGWith n k l m) {a b c d w : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hEmpty : ∀ z, ¬(G.Adj a z ∧ G.Adj b z))
    (hcw : G.Adj c w) (hdw : G.Adj d w) : False := by
  classical
  have : IsEmpty (G.commonNeighbors a b) := ⟨fun v => hEmpty v.val v.property⟩
  have hZero : l = 0 := (hSRG.of_adj a b hab).symm.trans Fintype.card_of_isEmpty
  have hPos : 0 < Fintype.card (G.commonNeighbors c d) :=
    Fintype.card_pos_iff.mpr ⟨⟨w, hcw, hdw⟩⟩
  rw [hSRG.of_adj c d hcd, hZero] at hPos
  exact (Nat.lt_irrefl 0) hPos

/-- A nonadjacent twin pair in a strongly regular graph forces its
complement to have complete components. -/
theorem srg_cocluster_of_false_twins {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k l m : ℕ}
    (hSRG : G.IsSRGWith n k l m) {a b : V} (hab : a ≠ b)
    (hna : ¬G.Adj a b) (hTwin : ∀ z, G.Adj a z ↔ G.Adj b z) :
    ∀ x y z, Gᶜ.Adj x y → Gᶜ.Adj y z → x ≠ z → Gᶜ.Adj x z := by
  classical
  let f : G.commonNeighbors a b ≃ G.neighborSet a :=
    { toFun := fun z => ⟨z.val, z.property.1⟩
      invFun := fun z => ⟨z.val, z.property, (hTwin z.val).mp z.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  have hEq : m = k :=
    (hSRG.of_not_adj hab hna).symm.trans ((Fintype.card_congr f).trans
      ((G.card_neighborSet_eq_degree a).trans (hSRG.regular a)))
  have hSame {x y : V} (hne : x ≠ y) (hnxy : ¬G.Adj x y) {z : V}
      (hxz : G.Adj x z) : G.Adj y z := by
    by_contra hNot
    let j : G.commonNeighbors x y → G.neighborSet x :=
      fun v => ⟨v.val, v.property.1⟩
    have hj : Function.Injective j := fun _ _ e =>
      Subtype.ext (congrArg (fun w : G.neighborSet x => w.val) e)
    have hLt := Fintype.card_lt_of_injective_of_notMem j hj
      (b := ⟨z, hxz⟩) (by
        rintro ⟨v, hv⟩
        have hvz : v.val = z := congrArg (fun w : G.neighborSet x => w.val) hv
        exact hNot (hvz ▸ v.property.2))
    rw [hSRG.of_not_adj hne hnxy, G.card_neighborSet_eq_degree x, hSRG.regular x, hEq] at hLt
    exact (Nat.lt_irrefl _) hLt
  intro x y z hxy hyz hxz
  exact ⟨hxz, fun hxzAdj => hyz.2 (hSame hxy.1 hxy.2 hxzAdj)⟩

/-- With at least two cliques, deleting all off-diagonal cross edges
leaves a nonedge with an empty common neighbourhood. -/
theorem srg_cover_off_empty_cluster {s t n k l m : ℕ} (X : CrossType)
    [DecidableRel (coverGraph s t X false).Adj]
    (hs : 2 ≤ s) (ht : 0 < t)
    (hSRG : (coverGraph s t X false).IsSRGWith n k l m) :
    ∀ x y z, (coverGraph s t X false).Adj x y →
      (coverGraph s t X false).Adj y z → x ≠ z →
      (coverGraph s t X false).Adj x z := by
  have key {v w : CoverVertex s t}
      (h : (coverGraph s t X false).Adj v w) : v.2.1 = w.2.1 := by
    rcases h with ⟨_, hIndex, _⟩ | ⟨_, hCross⟩
    · exact hIndex
    · by_contra hne
      simp [hne] at hCross
  let i : Fin s := ⟨0, by omega⟩
  let j : Fin s := ⟨1, by omega⟩
  let a : Fin t := ⟨0, ht⟩
  have hij : i ≠ j := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  refine srg_cluster_of_empty_common_nonedge _ hSRG
    (a := left i a) (b := left j a) ?_ ?_ ?_
  · exact fun h => hij (congrArg (fun v : CoverVertex s t => v.2.1) h)
  · exact fun h => hij (key h)
  · rintro v ⟨h₁, h₂⟩
    exact hij ((key h₁).trans (key h₂).symm)

/-- For empty diagonal cross blocks, the two vertices with a common clique
index on opposite sides have no common neighbour. -/
theorem srg_cover_diag_empty_cluster {s t n k l m : ℕ} (Y : Bool)
    [DecidableRel (coverGraph s t .empty Y).Adj]
    (hs : 0 < s) (ht : 0 < t)
    (hSRG : (coverGraph s t .empty Y).IsSRGWith n k l m) :
    ∀ x y z, (coverGraph s t .empty Y).Adj x y →
      (coverGraph s t .empty Y).Adj y z → x ≠ z →
      (coverGraph s t .empty Y).Adj x z := by
  let i : Fin s := ⟨0, hs⟩
  let a : Fin t := ⟨0, ht⟩
  refine srg_cluster_of_empty_common_nonedge _ hSRG
    (a := left i a) (b := right i a) (by simp [left, right])
    (by simp [cross_diag_iff, CrossType.rel]) ?_
  rintro ⟨side, j, b⟩ ⟨h₁, h₂⟩
  cases side <;>
    simp [coverGraph, coverAdj, CrossType.rel, left, right] at h₁ h₂
  · simp [h₁.1] at h₂
  · simp [h₂.1] at h₁

private theorem srg_false_of_common_injection {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k l m : ℕ}
    (hSRG : G.IsSRGWith n k l m) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (f : G.commonNeighbors a b ↪ G.commonNeighbors c d)
    (w : G.commonNeighbors c d) (hMissing : w ∉ Set.range f) : False := by
  have hLt := Fintype.card_lt_of_injective_of_notMem f f.injective hMissing
  rw [hSRG.of_adj a b hab, hSRG.of_adj c d hcd] at hLt
  exact (Nat.lt_irrefl _) hLt

/-- With at least two cliques and two coordinates, a diagonal matching
gives an edge in no triangle, whereas an off-diagonal edge lies in a triangle. -/
theorem srg_cover_off_full_matching_false {s t n k l m : ℕ}
    [DecidableRel (coverGraph s t .matching true).Adj]
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hSRG : (coverGraph s t .matching true).IsSRGWith n k l m) : False := by
  let i : Fin s := ⟨0, by omega⟩
  let j : Fin s := ⟨1, by omega⟩
  let a : Fin t := ⟨0, by omega⟩
  let b : Fin t := ⟨1, by omega⟩
  have hij : i ≠ j := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  have hab : a ≠ b := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  refine srg_false_of_mixed_triangle_edges _ hSRG
    (a := left i a) (b := right i a) (c := left i a) (d := right j a)
    (w := left i b) (by simp [cross_diag_iff, CrossType.rel])
    ((cross_off_iff _ _ _ _ _ _ hij).mpr rfl) ?_
    (by simpa [left_induced, cliqueUnion] using hab)
    ((adj_comm _ _ _).mpr ((cross_off_iff _ _ _ _ _ _ hij).mpr rfl))
  rintro ⟨side, k, c⟩ ⟨h₁, h₂⟩
  cases side <;> simp [coverGraph, coverAdj, left, right, CrossType.rel] at h₁ h₂
  · simp [h₁.1, h₁.2] at h₂
  · simp [h₂.1, h₂.2] at h₁

/-- In a co-matching, moving the right-side common neighbours of a
diagonal edge from clique i to clique j injects into the common
neighbours of the off-diagonal edge. The left vertex at the opposite
endpoint's coordinate is an additional common neighbour. -/
theorem srg_cover_off_full_comatching_false {s t n k l m : ℕ}
    [DecidableRel (coverGraph s t .coMatching true).Adj]
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hSRG : (coverGraph s t .coMatching true).IsSRGWith n k l m) : False := by
  let G := coverGraph s t .coMatching true
  let i : Fin s := ⟨0, by omega⟩
  let j : Fin s := ⟨1, by omega⟩
  let a : Fin t := ⟨0, by omega⟩
  let b : Fin t := ⟨1, by omega⟩
  have hij : i ≠ j := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  have hab : a ≠ b := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  have hd : G.Adj (left i a) (right i b) :=
    (cross_diag_iff _ _ _ _ _).mpr hab
  have ho : G.Adj (left i a) (right j b) :=
    (cross_off_iff _ _ _ _ _ _ hij).mpr rfl
  have hp (x : G.commonNeighbors (left i a) (right i b)) :
      x.val.2.1 = i ∧ a ≠ x.val.2.2 ∧ b ≠ x.val.2.2 := by
    rcases x with ⟨⟨side, k, c⟩, h₁, h₂⟩
    change G.Adj (left i a) (side, k, c) at h₁
    change G.Adj (right i b) (side, k, c) at h₂
    cases side <;>
      simp [G, coverGraph, coverAdj, CrossType.rel, left, right] at h₁ h₂
    · exact ⟨h₁.1.symm, h₁.2, by simpa [h₁.1] using h₂⟩
    · exact ⟨h₂.1.symm, by simpa [h₂.1] using h₁, h₂.2⟩
  let f : G.commonNeighbors (left i a) (right i b) ↪
      G.commonNeighbors (left i a) (right j b) :=
    { toFun := fun x => ⟨
        (x.val.1, (if x.val.1 = false then i else j, x.val.2.2)), by
          obtain ⟨_, ha, hb⟩ := hp x
          change G.Adj (left i a) (_, _, _) ∧ G.Adj (right j b) (_, _, _)
          cases h : x.val.1
          · simp [G, coverGraph, coverAdj, left, right, hij.symm, ha]
          · simp [G, coverGraph, coverAdj, left, right, hij, hb]⟩
      inj' := by
        intro x y h
        have q := congrArg Subtype.val h
        have hSide := congrArg Prod.fst q
        have hCoord := congrArg (fun v : CoverVertex s t => v.2.2) q
        have hIdx := (hp x).1.trans (hp y).1.symm
        exact Subtype.ext (Prod.ext hSide (Prod.ext hIdx hCoord)) }
  let w : G.commonNeighbors (left i a) (right j b) := ⟨left i b, by
    change G.Adj (left i a) (left i b) ∧ G.Adj (right j b) (left i b)
    simp [G, coverGraph, coverAdj, left, right, hij.symm, hab]⟩
  refine srg_false_of_common_injection _ hSRG hd ho f w ?_
  rintro ⟨x, hx⟩
  exact (hp x).2.2 ((congrArg (fun v : CoverVertex s t => v.2.2)
    (congrArg Subtype.val hx)).symm)

private theorem srg_cluster_of_true_twins {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k l m : ℕ}
    (hSRG : G.IsSRGWith n k l m) {a b : V} (hab : G.Adj a b)
    (hTwin : ∀ z, z ≠ a → z ≠ b → (G.Adj a z ↔ G.Adj b z)) :
    ∀ x y z, G.Adj x y → G.Adj y z → x ≠ z → G.Adj x z := by
  classical
  have hNot : ¬ Gᶜ.Adj a b := fun h => h.2 hab
  have hTwinsCompl (z : V) : Gᶜ.Adj a z ↔ Gᶜ.Adj b z := by
    by_cases hza : z = a
    · subst z
      simp [hab.symm]
    by_cases hzb : z = b
    · subst z
      simp [hab]
    exact and_congr ⟨fun _ h => hzb h.symm, fun _ h => hza h.symm⟩
      (not_congr (hTwin z hza hzb))
  simpa only [compl_compl] using
    srg_cocluster_of_false_twins Gᶜ hSRG.compl (G.ne_of_adj hab) hNot hTwinsCompl

/-- A full diagonal block gives adjacent twins whenever one half-clique
has at least two vertices. -/
theorem srg_cover_diag_full_cluster {s t n k l m : ℕ} (Y : Bool)
    [DecidableRel (coverGraph s t .full Y).Adj]
    (hs : 0 < s) (ht : 2 ≤ t)
    (hSRG : (coverGraph s t .full Y).IsSRGWith n k l m) :
    ∀ x y z, (coverGraph s t .full Y).Adj x y →
      (coverGraph s t .full Y).Adj y z → x ≠ z →
      (coverGraph s t .full Y).Adj x z := by
  let i : Fin s := ⟨0, hs⟩
  let a : Fin t := ⟨0, by omega⟩
  let b : Fin t := ⟨1, by omega⟩
  have hab : a ≠ b := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  refine srg_cluster_of_true_twins _ hSRG
    (a := left i a) (b := left i b) (by simpa [left_induced, cliqueUnion] using hab) ?_
  rintro ⟨side, j, c⟩ ha hb
  cases side
  · by_cases hij : i = j
    · subst j
      have hac : a ≠ c := by
        intro h
        exact ha (by simp [left, h])
      have hbc : b ≠ c := by
        intro h
        exact hb (by simp [left, h])
      simp [coverGraph, coverAdj, left, hac, hbc]
    · simp [coverGraph, coverAdj, left, hij]
  · simp [coverGraph, coverAdj, left, CrossType.rel]

/-- A one-clique co-matching cover has nonadjacent twins with the same
coordinate on opposite sides. -/
theorem srg_cover_one_clique_comatching {t n k l m : ℕ} (Y : Bool)
    [DecidableRel (coverGraph 1 t .coMatching Y).Adj]
    (ht : 0 < t)
    (hSRG : (coverGraph 1 t .coMatching Y).IsSRGWith n k l m) :
    ∀ x y z, (coverGraph 1 t .coMatching Y)ᶜ.Adj x y →
      (coverGraph 1 t .coMatching Y)ᶜ.Adj y z → x ≠ z →
      (coverGraph 1 t .coMatching Y)ᶜ.Adj x z := by
  let a : Fin t := ⟨0, ht⟩
  refine srg_cocluster_of_false_twins _ hSRG
    (a := left (0 : Fin 1) a) (b := right 0 a)
    (by simp [left, right]) (by simp [cross_diag_iff, CrossType.rel]) ?_
  rintro ⟨side, j, c⟩
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  cases side <;> simp [coverGraph, coverAdj, CrossType.rel, left, right]

private theorem srg_cover_one_clique_matching_false {t n k l m : ℕ} (Y : Bool)
    [DecidableRel (coverGraph 1 t .matching Y).Adj]
    (ht : 3 ≤ t)
    (hSRG : (coverGraph 1 t .matching Y).IsSRGWith n k l m) : False := by
  let a : Fin t := ⟨0, by omega⟩
  let b : Fin t := ⟨1, by omega⟩
  let c : Fin t := ⟨2, by omega⟩
  have hab : a ≠ b := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  have hac : a ≠ c := by
    intro h
    have hh := congrArg Fin.val h
    change 0 = 2 at hh
    omega
  have hbc : b ≠ c := by
    intro h
    have hh := congrArg Fin.val h
    change 1 = 2 at hh
    omega
  refine srg_false_of_mixed_triangle_edges _ hSRG
    (a := left 0 a) (b := right 0 a) (c := left 0 a) (d := left 0 b)
    (w := left 0 c) (by simp [cross_diag_iff, CrossType.rel])
    (by simpa [left_induced, cliqueUnion] using hab) ?_
    (by simpa [left_induced, cliqueUnion] using hac)
    (by simpa [left_induced, cliqueUnion] using hbc)
  rintro ⟨side, j, d⟩ ⟨h₁, h₂⟩
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  cases side <;>
    simp [coverGraph, coverAdj, left, right, CrossType.rel] at h₁ h₂
  · exact h₁ h₂
  · exact h₂ h₁

private theorem cover_one_coordinate_relabel (s : ℕ) (Y : Bool) :
    coverGraph s 1 .matching Y = coverGraph s 1 .full Y ∧
    coverGraph s 1 .coMatching Y = coverGraph s 1 .empty Y := by
  constructor <;> ext ⟨side₁, i, a⟩ ⟨side₂, j, b⟩
  all_goals
    have hab : a = b := Subsingleton.elim _ _
    subst b
    simp [coverGraph, coverAdj, CrossType.rel]

private theorem cover_full_one_coordinate (s : ℕ) :
    ∀ x y z, (coverGraph s 1 .full true)ᶜ.Adj x y →
      (coverGraph s 1 .full true)ᶜ.Adj y z → x ≠ z →
      (coverGraph s 1 .full true)ᶜ.Adj x z := by
  have hAdj (u v : CoverVertex s 1) :
      (coverGraph s 1 .full true).Adj u v ↔ u.1 ≠ v.1 := by
    simp [coverGraph, coverAdj, CrossType.rel, Subsingleton.elim u.2.2 v.2.2]
  intro x y z hxy hyz hxz
  refine ⟨hxz, ?_⟩
  have h₁ := Classical.not_not.mp (fun h => hxy.2 ((hAdj x y).mpr h))
  have h₂ := Classical.not_not.mp (fun h => hyz.2 ((hAdj y z).mpr h))
  exact fun h => (hAdj x z).mp h (h₁.trans h₂)

private theorem cover_full_one_clique (t : ℕ) :
    ∀ x y z, (coverGraph 1 t .full false).Adj x y →
      (coverGraph 1 t .full false).Adj y z → x ≠ z →
      (coverGraph 1 t .full false).Adj x z := by
  have hAdj (u v : CoverVertex 1 t) :
      (coverGraph 1 t .full false).Adj u v ↔ u ≠ v := by
    rcases u with ⟨side₁, i, a⟩
    rcases v with ⟨side₂, j, b⟩
    have hij : i = j := Subsingleton.elim _ _
    subst j
    cases side₁ <;> cases side₂ <;> simp [coverGraph, coverAdj, CrossType.rel]
  intro x _ z _ _ hxz
  exact (hAdj x z).mpr hxz

private theorem cover_one_clique_two_matching (Y : Bool) :
    ∀ x y z, (coverGraph 1 2 .matching Y)ᶜ.Adj x y →
      (coverGraph 1 2 .matching Y)ᶜ.Adj y z → x ≠ z →
      (coverGraph 1 2 .matching Y)ᶜ.Adj x z := by
  have hAdj (u v : CoverVertex 1 2) :
      (coverGraph 1 2 .matching Y)ᶜ.Adj u v ↔ u.1 ≠ v.1 ∧ u.2.2 ≠ v.2.2 := by
    rcases u with ⟨side₁, i, a⟩
    rcases v with ⟨side₂, j, b⟩
    have hi : i = j := Subsingleton.elim _ _
    subst j
    cases side₁ <;> cases side₂ <;>
      simp [coverGraph, coverAdj, CrossType.rel]
  rintro ⟨p, i, a⟩ ⟨q, j, b⟩ ⟨r, k, c⟩ hxy hyz hxz
  obtain ⟨hpq, hab⟩ := (hAdj _ _).mp hxy
  obtain ⟨hqr, hbc⟩ := (hAdj _ _).mp hyz
  have hpr : p = r := by
    cases p <;> cases q <;> cases r <;> simp_all
  have hac : a = c := by
    apply Fin.ext
    have h₁ : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have h₂ : b.val ≠ c.val := fun h => hbc (Fin.ext h)
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    omega
  exact (hxz (Prod.ext hpr (Prod.ext (Subsingleton.elim _ _) hac))).elim


/-- Strong regularity forces a generalized clique cover to be a union
of cliques or the complement of such a union. -/
theorem srg_cover_cluster_or_complement {s t n k l m : ℕ} (X : CrossType) (Y : Bool)
    [DecidableRel (coverGraph s t X Y).Adj]
    (hSRG : (coverGraph s t X Y).IsSRGWith n k l m) :
    (∀ x y z, (coverGraph s t X Y).Adj x y → (coverGraph s t X Y).Adj y z →
      x ≠ z → (coverGraph s t X Y).Adj x z) ∨
    (∀ x y z, (coverGraph s t X Y)ᶜ.Adj x y → (coverGraph s t X Y)ᶜ.Adj y z →
      x ≠ z → (coverGraph s t X Y)ᶜ.Adj x z) := by
  classical
  by_cases hs : 0 < s
  · by_cases ht : 0 < t
    · by_cases hSmallT : t = 1
      · subst t
        by_cases hY : Y = true
        · subst Y
          cases X with
          | empty => exact .inl (srg_cover_diag_empty_cluster _ hs ht hSRG)
          | full => exact .inr (cover_full_one_coordinate s)
          | matching => rw [(cover_one_coordinate_relabel s true).1]
                        exact .inr (cover_full_one_coordinate s)
          | coMatching =>
            have he := (cover_one_coordinate_relabel s true).2
            have hSRG' : ∃ n k l m, (coverGraph s 1 .empty true).IsSRGWith n k l m :=
              ⟨n, k, l, m, by simpa only [← he] using hSRG⟩
            obtain ⟨n', k', l', m', h⟩ := hSRG'
            rw [he]
            exact .inl (srg_cover_diag_empty_cluster _ hs ht h)
        · have hFalse : Y = false := by cases Y <;> simp_all
          subst Y
          by_cases hSmallS : s = 1
          · subst s
            cases X with
            | empty => exact .inl (srg_cover_diag_empty_cluster _ hs ht hSRG)
            | full => exact .inl (cover_full_one_clique 1)
            | matching => rw [(cover_one_coordinate_relabel 1 false).1]
                          exact .inl (cover_full_one_clique 1)
            | coMatching => exact .inr (srg_cover_one_clique_comatching _ ht hSRG)
          · exact .inl (srg_cover_off_empty_cluster _ (by omega) ht hSRG)
      · by_cases hSmallS : s = 1
        · subst s
          cases X with
          | empty => exact .inl (srg_cover_diag_empty_cluster _ hs ht hSRG)
          | full => exact .inl (srg_cover_diag_full_cluster _ hs (by omega) hSRG)
          | coMatching => exact .inr (srg_cover_one_clique_comatching _ ht hSRG)
          | matching =>
            by_cases hTwo : t = 2
            · subst t
              exact .inr (cover_one_clique_two_matching Y)
            · exact (srg_cover_one_clique_matching_false Y (by omega) hSRG).elim
        · cases Y with
          | false => exact .inl (srg_cover_off_empty_cluster _ (by omega) ht hSRG)
          | true =>
            cases X with
            | empty => exact .inl (srg_cover_diag_empty_cluster _ hs ht hSRG)
            | full => exact .inl (srg_cover_diag_full_cluster _ hs (by omega) hSRG)
            | matching =>
              exact (srg_cover_off_full_matching_false (by omega) (by omega) hSRG).elim
            | coMatching =>
              exact (srg_cover_off_full_comatching_false (by omega) (by omega) hSRG).elim
    · have : t = 0 := by omega
      subst t
      exact .inl (fun x => Fin.elim0 x.2.2)
  · have : s = 0 := by omega
    subst s
    exact .inl (fun x => Fin.elim0 x.2.1)

/-- The cluster alternatives have uniform component sizes, by the
vertex transitivity of generalized clique covers. -/
theorem srg_uniform_cover_homogeneous {s t n k l m : ℕ} (X : CrossType) (Y : Bool)
    [DecidableRel (coverGraph s t X Y).Adj]
    (hSRG : (coverGraph s t X Y).IsSRGWith n k l m) :
    DoubleCover.IsHomogeneousGraph (coverGraph s t X Y) := by
  have hTrans := CliqueCovers.uniform_cover_vertex_transitive s t X Y
  rcases srg_cover_cluster_or_complement X Y hSRG with h | h
  · exact BlockSystems.vertex_transitive_cluster_isHomogeneous _ hTrans h
  · exact (DoubleCover.homogeneous_complement_iff _).mpr
      (BlockSystems.vertex_transitive_cluster_isHomogeneous _
        (BlockSystems.transitive_complement _ hTrans) h)

/-- Transport strong regularity across graph equality and adjacency instances. -/
theorem srg_of_eq {V : Type*} [Fintype V] {G K : SimpleGraph V}
    [gDec : DecidableRel G.Adj] [kDec : DecidableRel K.Adj]
    {n k l m : ℕ} (heq : G = K) (h : G.IsSRGWith n k l m) :
    K.IsSRGWith n k l m := by
  subst K
  have hDec : gDec = kDec := Subsingleton.elim _ _
  exact hDec ▸ h

/-- The same conclusion holds when the complement of the cover is
strongly regular. -/
theorem srg_uniform_cover_compl_homogeneous {s t n k l m : ℕ} (X : CrossType) (Y : Bool)
    [DecidableRel (coverGraph s t X Y).Adj]
    (hSRG : (coverGraph s t X Y)ᶜ.IsSRGWith n k l m) :
    DoubleCover.IsHomogeneousGraph (coverGraph s t X Y)ᶜ := by
  have hCom := srg_of_eq (compl_compl _) hSRG.compl
  exact (DoubleCover.homogeneous_complement_iff _).mp
    (srg_uniform_cover_homogeneous X Y hCom)

/-- Strongly regular parameters are invariant under changing vertex labels. -/
theorem srg_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
    (φ : G ≃g H) {n k l m : ℕ} (h : G.IsSRGWith n k l m) : H.IsSRGWith n k l m := by
  have hAdj (x y : V) : G.Adj x y ↔ H.Adj (φ x) (φ y) :=
    φ.map_rel_iff.symm
  have hNeighbors (x : V) : Fintype.card (G.neighborSet x) =
      Fintype.card (H.neighborSet (φ x)) :=
    Fintype.card_congr (φ.toEquiv.subtypeEquiv (hAdj x))
  have hCommon (x y : V) : Fintype.card (G.commonNeighbors x y) =
      Fintype.card (H.commonNeighbors (φ x) (φ y)) :=
    Fintype.card_congr (φ.toEquiv.subtypeEquiv (fun z => and_congr (hAdj x z) (hAdj y z)))
  refine ⟨(Fintype.card_congr φ.toEquiv).symm.trans h.card, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨v, rfl⟩ := φ.toEquiv.surjective x
    change H.degree (φ v) = k
    calc
      H.degree (φ v) = Fintype.card (H.neighborSet (φ v)) :=
        (H.card_neighborSet_eq_degree _).symm
      _ = Fintype.card (G.neighborSet v) := (hNeighbors v).symm
      _ = G.degree v := G.card_neighborSet_eq_degree _
      _ = k := h.regular v
  · intro x y hAdjXY
    obtain ⟨u, rfl⟩ := φ.toEquiv.surjective x
    obtain ⟨v, rfl⟩ := φ.toEquiv.surjective y
    exact (hCommon u v).symm.trans (h.of_adj _ _ ((hAdj _ _).mpr hAdjXY))
  · intro x y hNe hNonadj
    obtain ⟨u, rfl⟩ := φ.toEquiv.surjective x
    obtain ⟨v, rfl⟩ := φ.toEquiv.surjective y
    exact (hCommon u v).symm.trans (h.of_not_adj (fun e => hNe (congrArg φ e))
      (fun a => hNonadj ((hAdj _ _).mp a)))

private theorem homogeneous_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (hH : DoubleCover.IsHomogeneousGraph H) : DoubleCover.IsHomogeneousGraph G := by
  have hSelf : IsEPPAEmbedding H H (Function.Embedding.refl W) := ⟨fun _ _ => Iff.rfl, hH⟩
  have hH' := eppa_relabel_host H (Function.Embedding.refl W) hSelf φ.symm
  have hG := eppa_relabel_base H G _ hH' φ.toEquiv G (fun _ _ => φ.map_rel_iff.symm)
  intro D p hp
  obtain ⟨q, hq, hFix⟩ := hG.2 D p hp
  refine ⟨q, hq, fun v hv => ?_⟩
  simpa [relabelEmbedding] using hFix v hv

/-- A strongly regular host is homogeneous if it is isomorphic to a
generalized clique cover or to its complement. -/
theorem srg_iso_cover_homogeneous {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k l m s t : ℕ}
    (hSRG : G.IsSRGWith n k l m) (X : CrossType) (Y : Bool)
    (hIso : Nonempty (G ≃g coverGraph s t X Y) ∨
      Nonempty (G ≃g (coverGraph s t X Y)ᶜ)) :
    DoubleCover.IsHomogeneousGraph G := by
  classical
  rcases hIso with hIso | hIso
  · obtain ⟨φ⟩ := hIso
    exact homogeneous_of_iso φ (srg_uniform_cover_homogeneous X Y (srg_of_iso φ hSRG))
  · obtain ⟨φ⟩ := hIso
    exact homogeneous_of_iso φ (srg_uniform_cover_compl_homogeneous X Y (srg_of_iso φ hSRG))

/-- Positive nonedge codegree forces an induced two-edge path as soon as a
nonedge exists. The order and degree hypotheses ensure there is a nonedge. -/
private theorem srg_not_cluster_of_positive_mu {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) (hOrder : k + 1 < n) (hMu : 0 < m) :
    ¬ BlockSystems.IsClusterGraph G := by
  classical
  intro hCluster
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp (h.card.symm ▸ (show 0 < n by omega))
  have hNonneighbors : 0 < Fintype.card (Gᶜ.neighborSet x) := by
    rw [Gᶜ.card_neighborSet_eq_degree, h.compl.regular]
    omega
  obtain ⟨⟨y, hxy⟩⟩ := Fintype.card_pos_iff.mp hNonneighbors
  have hCommon : 0 < Fintype.card (G.commonNeighbors x y) := by
    rw [h.of_not_adj hxy.1 hxy.2]
    exact hMu
  obtain ⟨⟨z, hxz, hyz⟩⟩ := Fintype.card_pos_iff.mp hCommon
  exact hxy.2 (hCluster x z y hxz hyz.symm hxy.1)

/-- An SRG with a positive common-neighbour count on each side of a
nontrivial adjacency relation cannot be a clique union or a cover, in either
orientation. -/
theorem srg_positive_codegrees_exclude_forms {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n k l m : ℕ}
    (h : G.IsSRGWith n k l m) (hDegree : 0 < k) (hOrder : k + 1 < n)
    (hMu : 0 < m) (hMuCompl : 2 * k - l < n) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  have hExcludes {W : Type} [Fintype W] (J : SimpleGraph W) [DecidableRel J.Adj]
      (hJ : J.IsSRGWith n k l m) :
      ¬ BlockSystems.IsClusterGraph J ∧ ¬ BlockSystems.IsClusterGraph Jᶜ :=
    ⟨srg_not_cluster_of_positive_mu J hJ hOrder hMu,
      srg_not_cluster_of_positive_mu Jᶜ hJ.compl (by omega) (by omega)⟩
  have hUnion (s t : ℕ) : BlockSystems.IsClusterGraph (cliqueUnion s t) := by
    intro x y z hxy hyz hxz
    change x.1 = y.1 ∧ x.2 ≠ y.2 at hxy
    change y.1 = z.1 ∧ y.2 ≠ z.2 at hyz
    exact ⟨hxy.1.trans hyz.1, fun h₂ => hxz (Prod.ext (hxy.1.trans hyz.1) h₂)⟩
  refine ⟨fun s t => ⟨?_⟩, fun s t => ⟨?_⟩, fun s t X Y => ⟨?_⟩,
    fun s t X Y => ⟨?_⟩⟩
  · intro f
    exact (hExcludes _ (srg_of_iso f h)).1 (hUnion _ _)
  · intro f
    apply (hExcludes _ (srg_of_iso f h)).2
    simpa only [compl_compl] using hUnion s t
  · intro f
    have hJ := srg_of_iso f h
    rcases srg_cover_cluster_or_complement X Y hJ with hc | hc
    · exact (hExcludes _ hJ).1 hc
    · exact (hExcludes _ hJ).2 hc
  · intro f
    have hJ := srg_of_iso f h
    have hJ' := srg_of_eq (compl_compl _) hJ.compl
    rcases srg_cover_cluster_or_complement X Y hJ' with hc | hc
    · exact (hExcludes _ hJ).2 (by simpa only [compl_compl, BlockSystems.IsClusterGraph] using hc)
    · exact (hExcludes _ hJ).1 hc

end EPPAIII.Primitive
