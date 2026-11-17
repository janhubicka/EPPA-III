import EPPAIII.Primitive.TriangularObstruction
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# The root graph of a triangular selection

Its vertices are the points of the host and its edges are the selected
two-element subsets. The finite edge count and line graph are identified with
the selected vertices via the same bijection.
-/

namespace EPPAIII.Primitive

open Sym2

/-- The graph whose edges are the selected pairs on the triangular host's points. -/
def triangularRootGraph {V : Type*} [DecidableEq V]
    (S : Set (TwoSet V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e : Sym2 V | ∃ h : ¬e.IsDiag,
    (⟨e.toFinset, Sym2.card_toFinset_of_not_isDiag e h⟩ : TwoSet V) ∈ S}

private theorem mem_triangularRootGraph_edgeSet {V : Type*} [DecidableEq V]
    (S : Set (TwoSet V)) (e : Sym2 V) :
    e ∈ (triangularRootGraph S).edgeSet ↔ ∃ h : ¬e.IsDiag,
      (⟨e.toFinset, Sym2.card_toFinset_of_not_isDiag e h⟩ : TwoSet V) ∈ S := by
  rw [triangularRootGraph, SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨fun h => h.1, fun h => ⟨h, h.choose⟩⟩

/-- An edge of the root graph is exactly a selected pair of distinct points. -/
theorem triangularRootGraph_adj {V : Type*} [DecidableEq V]
    (S : Set (TwoSet V)) {x y : V} (hxy : x ≠ y) :
    (triangularRootGraph S).Adj x y ↔ triangularPair x y hxy ∈ S := by
  rw [← SimpleGraph.mem_edgeSet, mem_triangularRootGraph_edgeSet]
  constructor
  · intro h
    obtain ⟨hd, hs⟩ := h
    have he : (⟨s(x, y).toFinset, Sym2.card_toFinset_of_not_isDiag _ hd⟩ : TwoSet V) =
        triangularPair x y hxy := Subtype.ext Sym2.toFinset_mk_eq
    exact he ▸ hs
  · intro hs
    have hd : ¬s(x, y).IsDiag := by simpa only [Sym2.mk_isDiag_iff] using hxy
    refine ⟨hd, ?_⟩
    have he : (⟨s(x, y).toFinset, Sym2.card_toFinset_of_not_isDiag _ hd⟩ : TwoSet V) =
        triangularPair x y hxy := Subtype.ext Sym2.toFinset_mk_eq
    exact he.symm ▸ hs

/-- The canonical bijection from the root graph's edges to the selected pairs. -/
noncomputable def triangularRootGraphEdgeEquiv {V : Type*} [DecidableEq V]
    (S : Set (TwoSet V)) : (triangularRootGraph S).edgeSet ≃ S :=
  Equiv.ofBijective (fun e => ⟨⟨e.val.toFinset, Sym2.card_toFinset_of_not_isDiag _
      ((triangularRootGraph S).not_isDiag_of_mem_edgeSet e.property)⟩,
    (mem_triangularRootGraph_edgeSet S e.val).mp e.property |>.choose_spec⟩) (by
      constructor
      · intro e f h
        apply Subtype.ext
        apply Sym2.ext
        intro x
        have hf : e.val.toFinset = f.val.toFinset :=
          congrArg (fun a : S => a.val.val) h
        rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, hf]
      · intro p
        obtain ⟨x, y, hxy, hp⟩ := Finset.card_eq_two.mp p.val.property
        have he : p.val = triangularPair x y hxy := Subtype.ext hp
        have hp' : triangularPair x y hxy ∈ S := he ▸ p.property
        have hAdj := (triangularRootGraph_adj S hxy).mpr hp'
        refine ⟨⟨s(x, y), hAdj⟩, ?_⟩
        exact Subtype.ext (Subtype.ext (Sym2.toFinset_mk_eq.trans hp.symm)))

/-- The selected subgraph is the line graph of its root graph. -/
noncomputable def triangularRootGraphLineGraphIso {V : Type*} [DecidableEq V]
    (S : Set (TwoSet V)) :
    (triangularRootGraph S).lineGraph ≃g (triangularGraph V).induce S where
  toEquiv := triangularRootGraphEdgeEquiv S
  map_rel_iff' := by
    intro x y
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    change
      (((triangularRootGraphEdgeEquiv S x).val ≠ (triangularRootGraphEdgeEquiv S y).val) ∧
        ∃ a, a ∈ x.val.toFinset ∧ a ∈ y.val.toFinset) ↔
      (x ≠ y ∧ ∃ a, a ∈ x.val ∧ a ∈ y.val)
    simp only [Sym2.mem_toFinset]
    exact and_congr ⟨fun h e => h (congrArg (fun z => (triangularRootGraphEdgeEquiv S z).val) e),
      fun h e => h ((triangularRootGraphEdgeEquiv S).injective (Subtype.ext e))⟩ Iff.rfl

/-- The corrected edge-set condition is triangle-freeness of the root graph. -/
theorem triangularRootGraph_cliqueFree_iff {V : Type*} [DecidableEq V]
    (S : Set (TwoSet V)) :
    (triangularRootGraph S).CliqueFree 3 ↔ TriangleFreeEdges S := by
  constructor
  · intro h x y z hxy hxz hyz h₁ h₂ h₃
    apply h ({x, y, z} : Finset V)
    have hCard : ({x, y, z} : Finset V).card = 3 :=
      Finset.card_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
    refine ⟨?_, hCard⟩
    have hxy' := (triangularRootGraph_adj S hxy).mpr h₁
    have hxz' := (triangularRootGraph_adj S hxz).mpr h₂
    have hyz' := (triangularRootGraph_adj S hyz).mpr h₃
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | contradiction | assumption | (apply SimpleGraph.Adj.symm; assumption)
  · intro h t ht
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
    exact h hxy hxz hyz
      ((triangularRootGraph_adj S hxy).mp (ht.isClique (by simp) (by simp) hxy))
      ((triangularRootGraph_adj S hxz).mp (ht.isClique (by simp) (by simp) hxz))
      ((triangularRootGraph_adj S hyz).mp (ht.isClique (by simp) (by simp) hyz))

/-- The Mantel bound for the order of a triangle-free triangular selection. -/
theorem card_triangularSelection_le_mantel {V : Type*} [Fintype V] [DecidableEq V]
    (S : Set (TwoSet V)) [Fintype S] (h : TriangleFreeEdges S) :
    Fintype.card S ≤ Fintype.card V ^ 2 / 4 := by
  classical
  have hc := SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2)
    ((triangularRootGraph_cliqueFree_iff S).mpr h)
  rw [SimpleGraph.edgeFinset_card, Fintype.card_congr (triangularRootGraphEdgeEquiv S),
    SimpleGraph.turanNumber_two] at hc
  exact hc

end EPPAIII.Primitive
