import EPPAIII.EPPA.Definitions
import EPPAIII.Primitive.IntersectionProfiles

/-!
# Triangular EPPA witnesses

The edge sets refer to the given embedding in the triangular host. The
hypothesis rules out a triangle of edges of the underlying graph on points.
-/

namespace EPPAIII.Primitive

abbrev TwoSet (V : Type*) := {e : Finset V // e.card = 2}

/-- Adjacency of two distinct two-element sets with a common point. -/
def triangularGraph (V : Type*) : SimpleGraph (TwoSet V) where
  Adj a b := a ≠ b ∧ ∃ x, x ∈ a.val ∧ x ∈ b.val
  symm := by
    constructor
    rintro a b ⟨hne, x, ha, hb⟩
    exact ⟨hne.symm, x, hb, ha⟩
  loopless := ⟨fun _ ha => ha.1 rfl⟩

private theorem twoSet_eq_pair {V : Type*} [DecidableEq V] {a : TwoSet V}
    {x y : V} (hx : x ∈ a.val) (hy : y ∈ a.val) (hxy : x ≠ y) :
    a.val = {x, y} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  · simp [a.property, hxy]

/-- Two distinct two-element sets have at most one common point. -/
private theorem common_point_unique {V : Type*} {a b : TwoSet V} (hab : a ≠ b)
    {x y : V} (hxa : x ∈ a.val) (hxb : x ∈ b.val)
    (hya : y ∈ a.val) (hyb : y ∈ b.val) : x = y := by
  classical
  by_contra hxy
  exact hab (Subtype.ext ((twoSet_eq_pair hxa hya hxy).trans
    (twoSet_eq_pair hxb hyb hxy).symm))

/-- The selected pairs, viewed as edges on points, contain no triangle. -/
def TriangleFreeEdges {V : Type*} [DecidableEq V] (S : Set (TwoSet V)) : Prop :=
  ∀ ⦃x y z : V⦄ (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z),
    (⟨{x, y}, by simp [hxy]⟩ : TwoSet V) ∈ S →
    (⟨{x, z}, by simp [hxz]⟩ : TwoSet V) ∈ S →
    (⟨{y, z}, by simp [hyz]⟩ : TwoSet V) ∈ S → False

/-- Pairwise intersecting selected edges have a common point. -/
theorem exists_common_point_of_triangularClique {V I : Type*} [DecidableEq V]
    {S : Set (TwoSet V)} (hS : TriangleFreeEdges S)
    (A : I ↪ S) {J : Finset I} (hJ : 1 < J.card)
    (hClique : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (triangularGraph V).Adj (A i).val (A j).val) :
    ∃ x, ∀ i ∈ J, x ∈ (A i).val.val := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hJ
  obtain ⟨hne, x, hxi, hxj⟩ := hClique i hi j hj hij
  refine ⟨x, fun l hl => ?_⟩
  by_cases hli : l = i
  · simpa [hli] using hxi
  by_cases hlj : l = j
  · simpa [hlj] using hxj
  by_contra hxl
  obtain ⟨_, y, hyl, hyi⟩ := hClique l hl i hi hli
  obtain ⟨_, z, hzl, hzj⟩ := hClique l hl j hj hlj
  have hxy : x ≠ y := fun e => hxl (e.symm ▸ hyl)
  have hxz : x ≠ z := fun e => hxl (e.symm ▸ hzl)
  have hyz : y ≠ z := by
    intro e
    subst z
    exact hxy (common_point_unique hne hxi hxj hyi hzj)
  have hi_eq : (A i).val = ⟨{x, y}, by simp [hxy]⟩ :=
    Subtype.ext (twoSet_eq_pair hxi hyi hxy)
  have hj_eq : (A j).val = ⟨{x, z}, by simp [hxz]⟩ :=
    Subtype.ext (twoSet_eq_pair hxj hzj hxz)
  have hl_eq : (A l).val = ⟨{y, z}, by simp [hyz]⟩ :=
    Subtype.ext (twoSet_eq_pair hyl hzl hyz)
  exact hS hxy hxz hyz (hi_eq ▸ (A i).property)
    (hj_eq ▸ (A j).property) (hl_eq ▸ (A l).property)

private theorem intersection_card_of_clique {V I : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq I] {S : Set (TwoSet V)} (hS : TriangleFreeEdges S)
    (A : I ↪ S) {J : Finset I} (hJ : 1 < J.card)
    (hClique : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (triangularGraph V).Adj (A i).val (A j).val) :
    (Finset.univ.filter fun x => ∀ i ∈ J, x ∈ (A i).val.val).card = 1 := by
  classical
  obtain ⟨x, hx⟩ := exists_common_point_of_triangularClique hS A hJ hClique
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hJ
  have hne : (A i).val ≠ (A j).val := fun e => hij (A.injective (Subtype.ext e))
  suffices (Finset.univ.filter fun y => ∀ k ∈ J, y ∈ (A k).val.val) = {x} by
    simp [this]
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun hy => common_point_unique hne (hy i hi) (hy j hj) (hx i hi) (hx j hj),
    fun h => h.symm ▸ hx⟩

private theorem intersection_card_of_not_clique {V I : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq I] {S : Set (TwoSet V)} (A : I ↪ S) (J : Finset I)
    (h : ¬ ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (triangularGraph V).Adj (A i).val (A j).val) :
    (Finset.univ.filter fun x => ∀ i ∈ J, x ∈ (A i).val.val).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply h
  intro i hi j hj hij
  have hx' := (Finset.mem_filter.mp hx).2
  exact ⟨fun e => hij (A.injective (Subtype.ext e)), x, hx' i hi, hx' j hj⟩

private def twoSetPerm {V : Type*} (e : Equiv.Perm V) : Equiv.Perm (TwoSet V) where
  toFun a := ⟨a.val.map e.toEmbedding, by simp [a.property]⟩
  invFun a := ⟨a.val.map e.symm.toEmbedding, by simp [a.property]⟩
  left_inv a := by
    apply Subtype.ext
    ext x
    simp
  right_inv a := by
    apply Subtype.ext
    ext x
    simp

private theorem twoSetPerm_automorphism {V : Type*} (e : Equiv.Perm V) :
    IsGraphAutomorphism (triangularGraph V) (twoSetPerm e) := by
  classical
  intro a b
  change (a ≠ b ∧ ∃ x, x ∈ a.val ∧ x ∈ b.val) ↔
    (twoSetPerm e a ≠ twoSetPerm e b ∧
      ∃ x, x ∈ a.val.map e.toEmbedding ∧ x ∈ b.val.map e.toEmbedding)
  simp only [Finset.mem_map_equiv]
  constructor
  · rintro ⟨hne, x, ha, hb⟩
    exact ⟨(twoSetPerm e).injective.ne hne, e x, by simpa, by simpa⟩
  · rintro ⟨hne, x, ha, hb⟩
    exact ⟨fun h => hne (congrArg (twoSetPerm e) h), e.symm x, ha, hb⟩

/-- The triangular host extends every partial automorphism of a selection whose
edges on the underlying points form a triangle-free graph. -/
theorem triangularGraph_eppa_induce {V : Type*} [Fintype V] [DecidableEq V]
    (S : Set (TwoSet V)) [Fintype S] (hS : TriangleFreeEdges S) :
    IsEPPAEmbedding ((triangularGraph V).induce S) (triangularGraph V)
      ⟨Subtype.val, Subtype.val_injective⟩ := by
  classical
  refine ⟨fun _ _ => Iff.rfl, ?_⟩
  intro D p hp
  let A : D ↪ S := ⟨Subtype.val, Subtype.val_injective⟩
  let B : D ↪ S := A.trans p.toEmbedding
  have hClique (J : Finset D) : (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (triangularGraph V).Adj (A i).val (A j).val) ↔
      (∀ i ∈ J, ∀ j ∈ J, i ≠ j →
      (triangularGraph V).Adj (B i).val (B j).val) := by
    constructor
    · intro h i hi j hj hij
      exact (hp i.val j.val i.property j.property).mp (h i hi j hj hij)
    · intro h i hi j hj hij
      exact (hp i.val j.val i.property j.property).mpr (h i hi j hj hij)
  obtain ⟨e, he⟩ := exists_perm_of_intersection_card_eq
    (fun i : D => (A i).val.val) (fun i : D => (B i).val.val) (by
      intro J
      by_cases hJ : 1 < J.card
      · by_cases h : ∀ i ∈ J, ∀ j ∈ J, i ≠ j →
          (triangularGraph V).Adj (A i).val (A j).val
        · rw [intersection_card_of_clique hS A hJ h,
            intersection_card_of_clique hS B hJ ((hClique J).mp h)]
        · rw [intersection_card_of_not_clique A J h,
            intersection_card_of_not_clique B J (fun hb => h ((hClique J).mpr hb))]
      · by_cases h0 : J.card = 0
        · simp [Finset.card_eq_zero.mp h0]
        · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (by omega : J.card = 1)
          simp [(A i).val.property, (B i).val.property])
  exact ⟨twoSetPerm e, twoSetPerm_automorphism e,
    fun i hi => Subtype.ext (he ⟨i, hi⟩)⟩

end EPPAIII.Primitive
