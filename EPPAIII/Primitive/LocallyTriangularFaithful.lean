import EPPAIII.Primitive.PointStabilizerTransport
import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.TriangularAutomorphisms
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-! # Faithfulness of a locally triangular point stabilizer when `μ = 6` -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- The common neighbours of two disjoint pairs are the four cross pairs. -/
theorem triangularGraph_card_common_of_not_adj {V : Type*} [DecidableEq V]
    (a b : TwoSet V) (hne : a ≠ b) (hn : ¬ (triangularGraph V).Adj a b) :
    Nat.card ((triangularGraph V).commonNeighbors a b) = 4 := by
  have hDisjoint (x : V) (ha : x ∈ a.val) (hb : x ∈ b.val) : False :=
    hn ⟨hne, x, ha, hb⟩
  let pair (p : a.val × b.val) := triangularPair p.1.val p.2.val
    (fun h => hDisjoint p.1 p.1.property (h.symm ▸ p.2.property))
  let f (p : a.val × b.val) : (triangularGraph V).commonNeighbors a b := ⟨pair p,
    ⟨fun he => hDisjoint p.2 (Eq.mp (congrArg (fun z : TwoSet V => p.2.val ∈ z.val) he.symm)
        (by simp [pair, triangularPair])) p.2.property,
      p.1, p.1.property, by simp [pair, triangularPair]⟩,
    ⟨fun he => hDisjoint p.1 p.1.property
      (Eq.mp (congrArg (fun z : TwoSet V => p.1.val ∈ z.val) he.symm)
        (by simp [pair, triangularPair])),
      p.2, p.2.property, by simp [pair, triangularPair]⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      have hPairs := congrArg (fun p : (triangularGraph V).commonNeighbors a b => p.val.val) hpq
      change ({p.1.val,p.2.val} : Finset V) = {q.1.val,q.2.val} at hPairs
      have h₁ : p.1.val ∈ ({q.1.val,q.2.val} : Finset V) := by
        rw [← hPairs]
        simp
      have h₂ : p.2.val ∈ ({q.1.val,q.2.val} : Finset V) := by
        rw [← hPairs]
        simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
      exact Prod.ext (Subtype.ext (h₁.resolve_right (fun h =>
        hDisjoint p.1 p.1.property (h.symm ▸ q.2.property))))
        (Subtype.ext (h₂.resolve_left (fun h =>
          hDisjoint p.2 (h.symm ▸ q.1.property) p.2.property)))
    · intro z
      obtain ⟨_, x, hxa, hxz⟩ := z.property.1
      obtain ⟨_, y, hyb, hyz⟩ := z.property.2
      have hxy : x ≠ y := fun h => hDisjoint x hxa (h.symm ▸ hyb)
      exact ⟨(⟨x,hxa⟩,⟨y,hyb⟩), Subtype.ext
        (triangularPair_of_mem hxz hyz hxy).symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_coe,
    a.property, b.property]

private def commonFinset {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (a b : W) : Finset W :=
  (H.commonNeighbors a b).toFinset

@[simp]
private theorem mem_commonFinset {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {a b z : W} :
    z ∈ commonFinset H a b ↔ H.Adj a z ∧ H.Adj b z := by
  exact Set.mem_toFinset

private theorem card_local_common_four {W V : Type*} [Fintype W] [DecidableEq V]
    (H : SimpleGraph W) [DecidableRel H.Adj] (r a b : W)
    (φ : localGraph H r ≃g triangularGraph V)
    (hab : a ≠ b) (hn : ¬ H.Adj a b) (ha : H.Adj r a) (hb : H.Adj r b) :
    ((commonFinset H a b).filter (H.Adj r)).card = 4 := by
  let A : H.neighborSet r := ⟨a, ha⟩
  let B : H.neighborSet r := ⟨b, hb⟩
  let S := (commonFinset H a b).filter (H.Adj r)
  let T := (triangularGraph V).commonNeighbors (φ A) (φ B)
  have hφA : φ A ≠ φ B := φ.injective.ne (fun h => hab (congrArg Subtype.val h))
  have hφN : ¬ (triangularGraph V).Adj (φ A) (φ B) := fun h => hn (φ.map_rel_iff.mp h)
  let e : S ≃ T :=
    { toFun := fun x => by
        let hMem := Finset.mem_filter.mp x.property
        let hAdj := (mem_commonFinset H).mp hMem.1
        let y : H.neighborSet r := ⟨x.val,hMem.2⟩
        exact ⟨φ y, φ.map_rel_iff.mpr (show (localGraph H r).Adj A y from hAdj.1),
          φ.map_rel_iff.mpr (show (localGraph H r).Adj B y from hAdj.2)⟩
      invFun := fun x => by
        let y := φ.symm x.val
        have hA : (localGraph H r).Adj A y := φ.map_rel_iff.mp (by
          rw [φ.apply_symm_apply]
          exact x.property.1)
        have hB : (localGraph H r).Adj B y := φ.map_rel_iff.mp (by
          rw [φ.apply_symm_apply]
          exact x.property.2)
        exact ⟨y.val, Finset.mem_filter.mpr ⟨(mem_commonFinset H).mpr ⟨hA,hB⟩,y.property⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact congrArg (fun y : H.neighborSet r => y.val)
          (φ.symm_apply_apply ⟨x.val, (Finset.mem_filter.mp x.property).2⟩)
      right_inv := fun x => Subtype.ext (φ.apply_symm_apply x.val) }
  change S.card = 4
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  exact triangularGraph_card_common_of_not_adj _ _ hφA hφN

/-- In a locally triangular strongly regular graph with `μ = 6`, a
nonneighbour of the root is determined by its adjacency to the root's neighbours. -/
theorem locallyTriangular_nonneighbor_eq_of_profile {W V : Type*}
    [Fintype W] [DecidableEq V] (H : SimpleGraph W) [DecidableRel H.Adj]
    {n k l : ℕ} (hSRG : H.IsSRGWith n k l 6)
    (hLocal : ∀ r, Nonempty (localGraph H r ≃g triangularGraph V))
    (r y z : W) (hry : r ≠ y) (hrz : r ≠ z) (hnry : ¬ H.Adj r y) (hnrz : ¬ H.Adj r z)
    (hProfile : ∀ a, H.Adj r a → (H.Adj y a ↔ H.Adj z a)) : y = z := by
  classical
  have hSix (a b : W) (hab : a ≠ b) (hNo : ¬ H.Adj a b) :
      (commonFinset H a b).card = 6 := by
    rw [commonFinset, Set.toFinset_card, hSRG.of_not_adj hab hNo]
  let C := commonFinset H r y
  have hC : C.card = 6 := hSix r y hry hnry
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
  obtain ⟨hra,hya⟩ := (mem_commonFinset H).mp ha
  let D := C.filter (H.Adj a)
  have hD : D.card = 4 := card_local_common_four H a r y (hLocal a).some
    hry hnry hra.symm hya.symm
  obtain ⟨b, hb, hab, hNo⟩ : ∃ b ∈ C, b ≠ a ∧ ¬ H.Adj a b := by
    by_contra! hAll
    have hSub : C ⊆ insert a D := by
      intro b hb
      by_cases hEq : b = a
      · exact Finset.mem_insert.mpr (Or.inl hEq)
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hb,hAll b hb hEq⟩)
    have h := (Finset.card_le_card hSub).trans (Finset.card_insert_le _ _)
    omega
  obtain ⟨hrb,hyb⟩ := (mem_commonFinset H).mp hb
  let E := (commonFinset H a b).filter (H.Adj r)
  have hE : E.card = 4 := card_local_common_four H r a b (hLocal r).some hab.symm hNo hra hrb
  have hnE (x : W) (h : ¬ H.Adj r x) : x ∉ E := fun hx => h (Finset.mem_filter.mp hx).2
  by_contra hyz
  have hSub : insert r (insert y (insert z E)) ⊆ commonFinset H a b := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact (mem_commonFinset H).mpr ⟨hra.symm,hrb.symm⟩
    · exact (mem_commonFinset H).mpr ⟨hya.symm,hyb.symm⟩
    · exact (mem_commonFinset H).mpr
        ⟨((hProfile a hra).mp hya).symm, ((hProfile b hrb).mp hyb).symm⟩
    · exact (Finset.mem_filter.mp hx).1
  have hLarge := Finset.card_le_card hSub
  rw [Finset.card_insert_of_notMem (by simp [hry,hrz,hnE r (H.irrefl)]),
    Finset.card_insert_of_notMem (by simp [hyz,hnE y hnry]),
    Finset.card_insert_of_notMem (hnE z hnrz), hE, hSix a b hab.symm hNo] at hLarge
  omega

private def graphAutosAsEmptyStabilizer {W : Type*} (H : SimpleGraph W) :
    graphAutomorphisms H ≃ hostPointwiseStabilizer H ∅ where
  toFun p := ⟨p.val, p.property, by simp⟩
  invFun p := ⟨p.val, p.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_local_automorphisms_of_iso {W V : Type*}
    {H : SimpleGraph W} {K : SimpleGraph V} (φ : H ≃g K) :
    Nat.card (graphAutomorphisms H) = Nat.card (graphAutomorphisms K) := by
  rw [Nat.card_congr (graphAutosAsEmptyStabilizer H),
    Nat.card_congr (graphAutosAsEmptyStabilizer K),
    Nat.card_congr (hostPointwiseStabilizerEquiv φ ∅), Set.image_empty]

/-- The point stabilizer acts faithfully on the triangular neighbourhood. -/
theorem locallyTriangular_hostPointwiseStabilizer_card_le {W V : Type*}
    [Fintype W] [Fintype V] (H : SimpleGraph W) [DecidableRel H.Adj]
    {n k l : ℕ} (hSRG : H.IsSRGWith n k l 6) (hV : 5 ≤ Fintype.card V)
    (hLocal : ∀ r, Nonempty (localGraph H r ≃g triangularGraph V)) (r : W) :
    Nat.card (hostPointwiseStabilizer H {r}) ≤ (Fintype.card V).factorial := by
  classical
  let restrict (p : hostPointwiseStabilizer H {r}) : graphAutomorphisms (localGraph H r) := by
    have hFix : p.val r = r := p.property.2 r (by simp)
    let e := p.val.subtypeEquiv (fun x => by
      change H.Adj r x ↔ H.Adj r (p.val x)
      simpa only [hFix] using p.property.1 r x)
    exact ⟨e, fun a b => p.property.1 a b⟩
  have hInj : Function.Injective restrict := by
    intro p q he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hp : p.val r = r := p.property.2 r (by simp)
    have hq : q.val r = r := q.property.2 r (by simp)
    have hOn (a : W) (ha : H.Adj r a) : p.val a = q.val a :=
      congrArg (fun f : graphAutomorphisms (localGraph H r) => (f.val ⟨a,ha⟩).val) he
    by_cases hrx : r = x
    · subst x
      exact hp.trans hq.symm
    by_cases hx : H.Adj r x
    · exact hOn x hx
    have pAdj (a : W) : H.Adj r a ↔ H.Adj r (p.val a) := by
      simpa only [hp] using p.property.1 r a
    have qAdj (a : W) : H.Adj r a ↔ H.Adj r (q.val a) := by
      simpa only [hq] using q.property.1 r a
    apply locallyTriangular_nonneighbor_eq_of_profile H hSRG hLocal r _ _
      (by simpa only [hp] using p.val.injective.ne hrx)
      (by simpa only [hq] using q.val.injective.ne hrx)
      (fun h => hx ((pAdj x).mpr h)) (fun h => hx ((qAdj x).mpr h))
    intro a ha
    obtain ⟨b, rfl⟩ := p.val.surjective a
    have h := hOn b ((pAdj b).mpr ha)
    calc
      _ ↔ H.Adj x b := (p.property.1 x b).symm
      _ ↔ H.Adj (q.val x) (q.val b) := q.property.1 x b
      _ ↔ _ := by rw [h]
  have hBound := Nat.card_le_card_of_injective restrict hInj
  rw [card_local_automorphisms_of_iso (hLocal r).some] at hBound
  exact hBound.trans (triangularGraph_automorphism_card_le hV)

end EPPAIII.Primitive
