import EPPAIII.Primitive.RookModel
import EPPAIII.EPPA.Definitions
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Tauto

/-!
# Extending a selected rook isomorphism from its coordinate relations

A consistent choice of direction on all mapped edges determines two
partial permutations of the coordinates. Each extends independently.
It therefore suffices to test preservation of the relative directions
of two edges at a time.
-/

namespace EPPAIII.Primitive

private abbrev Cell (n : ℕ) := Fin n × Fin n

/-- Two rook edges have the same direction when both run along rows or
both along columns. -/
def rookSameDirection {n : ℕ} (a b c d : Cell n) : Prop :=
  (a.1 = b.1 ↔ c.1 = d.1)

/-- Every graph-preserving correspondence of two edges in the selected
set preserves whether the directions agree. The edges may share vertices. -/
def RookFourPointCondition {n : ℕ} (S : Set (Cell n)) : Prop :=
  ∀ u v : Fin 4 → S,
    (∀ i j, u i = u j ↔ v i = v j) →
    (∀ i j, (rookGraph n).Adj (u i).val (u j).val ↔ (rookGraph n).Adj (v i).val (v j).val) →
    (rookGraph n).Adj (u 0).val (u 1).val →
    (rookGraph n).Adj (u 2).val (u 3).val →
    (rookSameDirection (u 0).val (u 1).val (u 2).val (u 3).val ↔
      rookSameDirection (v 0).val (v 1).val (v 2).val (v 3).val)

private theorem exists_perm_of_sameFibres {ι A : Type*} [Finite A]
    (f g : ι → A) (h : ∀ i j, f i = f j ↔ g i = g j) :
    ∃ σ : Equiv.Perm A, ∀ i, σ (f i) = g i := by
  classical
  let image := Set.range f
  let repr (x : image) : ι := Classical.choose x.property
  have hRepr (x : image) : f (repr x) = x.val := Classical.choose_spec x.property
  let k (x : image) := g (repr x)
  have hk : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    exact (hRepr a).symm.trans (((h _ _).mpr hab).trans (hRepr b))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair Subtype.val k Subtype.val_injective hk
  refine ⟨σ, fun i => ?_⟩
  let x : image := ⟨f i, ⟨i, rfl⟩⟩
  exact (hσ x).trans ((h _ _).mp (hRepr x))

private theorem rook_edge_axes {n : ℕ} {x y : Cell n} (h : (rookGraph n).Adj x y) :
    x.2 = y.2 ↔ ¬ x.1 = y.1 := by
  refine ⟨fun hCol hRow => h.1 (Prod.ext hRow hCol), ?_⟩
  exact fun hRow => h.2.resolve_left hRow

private theorem rook_eq_of_no_edge {n : ℕ} {x y : Cell n} (hne : x ≠ y)
    (h : ¬ (rookGraph n).Adj x y) : x.1 ≠ y.1 ∧ x.2 ≠ y.2 :=
  ⟨fun hRow => h ⟨hne, Or.inl hRow⟩, fun hCol => h ⟨hne, Or.inr hCol⟩⟩

private theorem rookGraph_preserves_coordinates {n : ℕ}
    (r c : Equiv.Perm (Fin n)) :
    IsGraphAutomorphism (rookGraph n) (Equiv.prodCongr r c) := by
  intro a b
  change (a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2)) ↔
    (Equiv.prodCongr r c a ≠ Equiv.prodCongr r c b ∧
      (r a.1 = r b.1 ∨ c a.2 = c b.2))
  simp only [ne_eq, (Equiv.prodCongr r c).injective.eq_iff, r.injective.eq_iff, c.injective.eq_iff]

private theorem rookGraph_transpose_auto {n : ℕ} :
    IsGraphAutomorphism (rookGraph n) (Equiv.prodComm (Fin n) (Fin n)) := by
  intro a b
  change (a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2)) ↔
    (Equiv.prodComm (Fin n) (Fin n) a ≠ Equiv.prodComm (Fin n) (Fin n) b ∧
      (a.2 = b.2 ∨ a.1 = b.1))
  simp only [ne_eq, (Equiv.prodComm (Fin n) (Fin n)).injective.eq_iff, or_comm]

private theorem extend_consistent_axes {ι : Type*} {n : ℕ}
    (u v : ι → Cell n)
    (hRow : ∀ i j, (u i).1 = (u j).1 ↔ (v i).1 = (v j).1)
    (hCol : ∀ i j, (u i).2 = (u j).2 ↔ (v i).2 = (v j).2) :
    ∃ q : Equiv.Perm (Cell n), IsGraphAutomorphism (rookGraph n) q ∧
      ∀ i, q (u i) = v i := by
  obtain ⟨r, hr⟩ := exists_perm_of_sameFibres (fun i => (u i).1) (fun i => (v i).1) hRow
  obtain ⟨c, hc⟩ := exists_perm_of_sameFibres (fun i => (u i).2) (fun i => (v i).2) hCol
  exact ⟨Equiv.prodCongr r c, rookGraph_preserves_coordinates r c,
    fun i => Prod.ext (hr i) (hc i)⟩

private theorem extend_consistent_directions {ι : Type*} {n : ℕ}
    (u v : ι → Cell n) (hu : Function.Injective u) (hv : Function.Injective v)
    (hAdj : ∀ i j, (rookGraph n).Adj (u i) (u j) ↔ (rookGraph n).Adj (v i) (v j))
    (hDirection : ∀ a b c d, (rookGraph n).Adj (u a) (u b) →
      (rookGraph n).Adj (u c) (u d) →
      (rookSameDirection (u a) (u b) (u c) (u d) ↔ rookSameDirection (v a) (v b) (v c) (v d))) :
    ∃ q : Equiv.Perm (Cell n), IsGraphAutomorphism (rookGraph n) q ∧
      ∀ i, q (u i) = v i := by
  classical
  have hOrient :
      (∀ i j, (rookGraph n).Adj (u i) (u j) → ((u i).1 = (u j).1 ↔ (v i).1 = (v j).1)) ∨
      (∀ i j, (rookGraph n).Adj (u i) (u j) → ((u i).1 = (u j).1 ↔ ¬ (v i).1 = (v j).1)) := by
    by_cases hExists : ∃ a b, (rookGraph n).Adj (u a) (u b)
    · obtain ⟨a, b, hab⟩ := hExists
      by_cases hEdge : (u a).1 = (u b).1 ↔ (v a).1 = (v b).1
      · left
        intro i j hij
        have h := hDirection a b i j hab hij
        unfold rookSameDirection at h
        tauto
      · right
        intro i j hij
        have h := hDirection a b i j hab hij
        unfold rookSameDirection at h
        tauto
    · exact Or.inl fun i j hij => (hExists ⟨i, j, hij⟩).elim
  have hNonedge (i j : ι) (hne : i ≠ j) (hNot : ¬ (rookGraph n).Adj (u i) (u j)) :
      ((u i).1 ≠ (u j).1 ∧ (u i).2 ≠ (u j).2) ∧
        ((v i).1 ≠ (v j).1 ∧ (v i).2 ≠ (v j).2) :=
    ⟨rook_eq_of_no_edge (fun h => hne (hu h)) hNot,
      rook_eq_of_no_edge (fun h => hne (hv h)) (fun h => hNot ((hAdj i j).mpr h))⟩
  rcases hOrient with hOrient | hOrient
  · have hAxes (i j : ι) :
        ((u i).1 = (u j).1 ↔ (v i).1 = (v j).1) ∧
        ((u i).2 = (u j).2 ↔ (v i).2 = (v j).2) := by
      by_cases hEq : i = j
      · subst j
        simp
      by_cases hEdge : (rookGraph n).Adj (u i) (u j)
      · exact ⟨hOrient i j hEdge, (rook_edge_axes hEdge).trans
          ((not_congr (hOrient i j hEdge)).trans (rook_edge_axes ((hAdj i j).mp hEdge)).symm)⟩
      · obtain ⟨⟨huR, huC⟩, ⟨hvR, hvC⟩⟩ := hNonedge i j hEq hEdge
        simp [huR, huC, hvR, hvC]
    exact extend_consistent_axes u v (fun i j => (hAxes i j).1) (fun i j => (hAxes i j).2)
  · let swap := Equiv.prodComm (Fin n) (Fin n)
    have hAxes (i j : ι) :
        ((u i).1 = (u j).1 ↔ (v i).2 = (v j).2) ∧
        ((u i).2 = (u j).2 ↔ (v i).1 = (v j).1) := by
      by_cases hEq : i = j
      · subst j
        simp
      by_cases hEdge : (rookGraph n).Adj (u i) (u j)
      · have hUV := hOrient i j hEdge
        have hV := rook_edge_axes ((hAdj i j).mp hEdge)
        have hU := rook_edge_axes hEdge
        tauto
      · obtain ⟨⟨huR, huC⟩, ⟨hvR, hvC⟩⟩ := hNonedge i j hEq hEdge
        simp [huR, huC, hvR, hvC]
    obtain ⟨q, hq, hMap⟩ := extend_consistent_axes u (fun i => swap (v i))
      (fun i j => (hAxes i j).1) (fun i j => (hAxes i j).2)
    refine ⟨q.trans swap, fun a b => (hq a b).trans (rookGraph_transpose_auto _ _), fun i => ?_⟩
    change swap (q (u i)) = v i
    rw [hMap]
    rfl

/-- A checked four-point condition suffices for EPPA of a selected
subgraph of a square rook graph. -/
theorem rookGraph_eppa_of_fourPointCondition {n : ℕ} (S : Set (Cell n))
    (hFour : RookFourPointCondition S) :
    IsEPPAEmbedding ((rookGraph n).induce S) (rookGraph n) (Function.Embedding.subtype S) := by
  classical
  refine ⟨fun _ _ => Iff.rfl, ?_⟩
  intro D p hp
  let I := {x : S // x ∈ D}
  let u (i : I) : Cell n := i.val.val
  let v (i : I) : Cell n := (p i.val).val
  have hu : Function.Injective u := fun _ _ h => Subtype.ext (Subtype.ext h)
  have hv : Function.Injective v := fun _ _ h => Subtype.ext (p.injective (Subtype.ext h))
  have hAdj (i j : I) : (rookGraph n).Adj (u i) (u j) ↔ (rookGraph n).Adj (v i) (v j) :=
    hp i.val j.val i.property j.property
  obtain ⟨q, hq, hMap⟩ := extend_consistent_directions u v hu hv hAdj (by
    intro a b c d hab hcd
    let ix : Fin 4 → I := ![a, b, c, d]
    exact hFour (fun i => (ix i).val) (fun i => p (ix i).val)
      (fun _ _ => p.injective.eq_iff.symm) (fun i j => hAdj (ix i) (ix j)) hab hcd)
  exact ⟨q, hq, fun i hi => hMap ⟨i, hi⟩⟩


/-- Two designated edges have no cross edge. -/
private def rookCrossEmpty {n : ℕ} (a b c d : Cell n) : Prop :=
  ¬ (rookGraph n).Adj a c ∧ ¬ (rookGraph n).Adj a d ∧
    ¬ (rookGraph n).Adj b c ∧ ¬ (rookGraph n).Adj b d

private def rookCrossFork {n : ℕ} (a b c d : Cell n) : Prop :=
  ((rookGraph n).Adj a c ∧ (rookGraph n).Adj a d) ∨
    ((rookGraph n).Adj b c ∧ (rookGraph n).Adj b d) ∨
    ((rookGraph n).Adj a c ∧ (rookGraph n).Adj b c) ∨
    ((rookGraph n).Adj a d ∧ (rookGraph n).Adj b d)

private def rookCrossComplete {n : ℕ} (a b c d : Cell n) : Prop :=
  (rookGraph n).Adj a c ∧ (rookGraph n).Adj a d ∧
    (rookGraph n).Adj b c ∧ (rookGraph n).Adj b d

private theorem sameDirection_of_shared {n : ℕ} {a b c : Cell n}
    (hab : (rookGraph n).Adj a b) (hac : (rookGraph n).Adj a c) :
    rookSameDirection a b a c ↔ b = c ∨ (rookGraph n).Adj b c := by
  simp only [rookSameDirection, rookGraph, ne_eq, Prod.ext_iff] at *
  grind

private theorem sameDirection_of_nonempty_cross {n : ℕ} {a b c d : Cell n}
    (hab : (rookGraph n).Adj a b) (hcd : (rookGraph n).Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hCross : ¬ rookCrossEmpty a b c d) :
    rookSameDirection a b c d ↔ ¬ rookCrossFork a b c d ∨ rookCrossComplete a b c d := by
  have eac : (rookGraph n).Adj a c ↔ a.1 = c.1 ∨ a.2 = c.2 := by
    change (a ≠ c ∧ _) ↔ _
    simp [hac]
  have ead : (rookGraph n).Adj a d ↔ a.1 = d.1 ∨ a.2 = d.2 := by
    change (a ≠ d ∧ _) ↔ _
    simp [had]
  have ebc : (rookGraph n).Adj b c ↔ b.1 = c.1 ∨ b.2 = c.2 := by
    change (b ≠ c ∧ _) ↔ _
    simp [hbc]
  have ebd : (rookGraph n).Adj b d ↔ b.1 = d.1 ∨ b.2 = d.2 := by
    change (b ≠ d ∧ _) ↔ _
    simp [hbd]
  simp only [rookSameDirection, rookCrossFork, rookCrossComplete, eac, ead, ebc, ebd]
  simp only [rookCrossEmpty, eac, ead, ebc, ebd] at hCross
  simp only [rookGraph, ne_eq, Prod.ext_iff] at hab hcd hac had hbc hbd
  grind (splits := 20)


/-- Two designated edges form an induced matching of four cells. -/
def RookInducedMatching {n : ℕ} (a b c d : Cell n) : Prop :=
  (rookGraph n).Adj a b ∧ (rookGraph n).Adj c d ∧
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
    ¬ (rookGraph n).Adj a c ∧ ¬ (rookGraph n).Adj a d ∧
    ¬ (rookGraph n).Adj b c ∧ ¬ (rookGraph n).Adj b d

/-- A selection is EPPA when all its induced two-edge matchings have
the same relative direction. -/
theorem rookGraph_eppa_of_matchingDirection {n : ℕ} (S : Set (Cell n))
    (direction : Prop)
    (hDirection : ∀ a b c d : S, RookInducedMatching a.val b.val c.val d.val →
      (rookSameDirection a.val b.val c.val d.val ↔ direction)) :
    IsEPPAEmbedding ((rookGraph n).induce S) (rookGraph n) (Function.Embedding.subtype S) := by
  classical
  apply rookGraph_eppa_of_fourPointCondition S
  intro u v hEq hAdj h01 h23
  have eac : (u 0).val = (u 2).val ↔ (v 0).val = (v 2).val :=
    Subtype.val_injective.eq_iff.trans ((hEq 0 2).trans Subtype.val_injective.eq_iff.symm)
  have ead : (u 0).val = (u 3).val ↔ (v 0).val = (v 3).val :=
    Subtype.val_injective.eq_iff.trans ((hEq 0 3).trans Subtype.val_injective.eq_iff.symm)
  have ebc : (u 1).val = (u 2).val ↔ (v 1).val = (v 2).val :=
    Subtype.val_injective.eq_iff.trans ((hEq 1 2).trans Subtype.val_injective.eq_iff.symm)
  have ebd : (u 1).val = (u 3).val ↔ (v 1).val = (v 3).val :=
    Subtype.val_injective.eq_iff.trans ((hEq 1 3).trans Subtype.val_injective.eq_iff.symm)
  have v01 := (hAdj 0 1).mp h01
  have v23 := (hAdj 2 3).mp h23
  have shared {a b c d : Cell n}
      (hab : (rookGraph n).Adj a b) (hcd : (rookGraph n).Adj c d) :
      (a = c → (rookSameDirection a b c d ↔ b = d ∨ (rookGraph n).Adj b d)) ∧
      (a = d → (rookSameDirection a b c d ↔ b = c ∨ (rookGraph n).Adj b c)) ∧
      (b = c → (rookSameDirection a b c d ↔ a = d ∨ (rookGraph n).Adj a d)) ∧
      (b = d → (rookSameDirection a b c d ↔ a = c ∨ (rookGraph n).Adj a c)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro rfl
      exact sameDirection_of_shared hab hcd
    · rintro rfl
      simpa only [rookSameDirection, @eq_comm _ c.1 a.1] using
        sameDirection_of_shared hab ((rookGraph n).adj_symm hcd)
    · rintro rfl
      simpa only [rookSameDirection, @eq_comm _ b.1 a.1] using
        sameDirection_of_shared ((rookGraph n).adj_symm hab) hcd
    · rintro rfl
      simpa only [rookSameDirection, @eq_comm _ b.1 a.1, @eq_comm _ c.1 b.1] using
        sameDirection_of_shared ((rookGraph n).adj_symm hab) ((rookGraph n).adj_symm hcd)
  have huOverlap := shared h01 h23
  have hvOverlap := shared v01 v23
  by_cases hac : (u 0).val = (u 2).val
  · exact (huOverlap.1 hac).trans ((or_congr ebd (hAdj 1 3)).trans
      (hvOverlap.1 (eac.mp hac)).symm)
  by_cases had : (u 0).val = (u 3).val
  · exact (huOverlap.2.1 had).trans ((or_congr ebc (hAdj 1 2)).trans
      (hvOverlap.2.1 (ead.mp had)).symm)
  by_cases hbc : (u 1).val = (u 2).val
  · exact (huOverlap.2.2.1 hbc).trans ((or_congr ead (hAdj 0 3)).trans
      (hvOverlap.2.2.1 (ebc.mp hbc)).symm)
  by_cases hbd : (u 1).val = (u 3).val
  · exact (huOverlap.2.2.2 hbd).trans ((or_congr eac (hAdj 0 2)).trans
      (hvOverlap.2.2.2 (ebd.mp hbd)).symm)
  have hvc := fun h => hac (eac.mpr h)
  have hvd := fun h => had (ead.mpr h)
  have hvbc := fun h => hbc (ebc.mpr h)
  have hvbd := fun h => hbd (ebd.mpr h)
  have hEmpty : rookCrossEmpty (u 0).val (u 1).val (u 2).val (u 3).val ↔
      rookCrossEmpty (v 0).val (v 1).val (v 2).val (v 3).val := by
    simp only [rookCrossEmpty, hAdj 0 2, hAdj 0 3, hAdj 1 2, hAdj 1 3]
  by_cases hCross : rookCrossEmpty (u 0).val (u 1).val (u 2).val (u 3).val
  · exact (hDirection _ _ _ _ ⟨h01, h23, hac, had, hbc, hbd, hCross⟩).trans
      (hDirection _ _ _ _ ⟨v01, v23, hvc, hvd, hvbc, hvbd, hEmpty.mp hCross⟩).symm
  · have hu := sameDirection_of_nonempty_cross h01 h23 hac had hbc hbd hCross
    have hv := sameDirection_of_nonempty_cross v01 v23 hvc hvd hvbc hvbd
      (fun h => hCross (hEmpty.mpr h))
    refine hu.trans (Iff.trans ?_ hv.symm)
    simp only [rookCrossFork, rookCrossComplete, hAdj 0 2, hAdj 0 3, hAdj 1 2, hAdj 1 3]

end EPPAIII.Primitive
