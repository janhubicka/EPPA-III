import EPPAIII.Primitive.LocalRecognitionArithmetic
import EPPAIII.Primitive.Triangular
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-!
# The octahedral endpoint of triangular local recognition

The proof uses the four local common neighbours of opposite vertices and
adds the root. The resulting complement has degree one on eight vertices.
-/

namespace EPPAIII.Primitive

open SimpleGraph

private instance triangularFourAdj : DecidableRel (triangularGraph (Fin 4)).Adj := by
  intro x y
  change Decidable (x ≠ y ∧ ∃ z, z ∈ x.val ∧ z ∈ y.val)
  infer_instance

private def octahedronA : TwoSet (Fin 4) := ⟨{0, 1}, by decide⟩
private def octahedronB : TwoSet (Fin 4) := ⟨{2, 3}, by decide⟩

/-- Recognize the octahedral endpoint from one actual rooted constituent.
Degree one in the complement gives the perfect matching of four pairs. -/
theorem locallyTriangular_four_recognition
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n k l μ : ℕ} (h : G.IsSRGWith n k l μ) (root : V)
    (iso : triangularGraph (Fin 4) ≃g G.induce (G.neighborSet root)) :
    n = 8 ∧ k = 6 ∧ l = 4 ∧ μ = 6 ∧ Gᶜ.IsRegularOfDegree 1 := by
  let a := iso octahedronA
  let b := iso octahedronB
  have hk : k = 6 := by
    rw [← h.regular root, ← G.card_neighborSet_eq_degree]
    exact iso.card_eq.symm.trans (by decide)
  have hl : l = 4 := by
    let equiv : (G.induce (G.neighborSet root)).neighborSet a ≃ G.commonNeighbors root a :=
      { toFun y := ⟨y.val.val, y.val.property, y.property⟩
        invFun y := ⟨⟨y.val, y.property.1⟩, y.property.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    rw [← h.of_adj root a a.property, ← Fintype.card_congr equiv,
      ← Fintype.card_congr (iso.mapNeighborSet octahedronA)]
    decide
  have hab : (a : V) ≠ b := fun hEq =>
    (by decide : octahedronA ≠ octahedronB) (iso.injective (Subtype.ext hEq))
  have hNonadj : ¬ G.Adj a b := fun hAdj =>
    (by decide : ¬ (triangularGraph (Fin 4)).Adj octahedronA octahedronB)
      (iso.map_rel_iff.mp hAdj)
  let common := (triangularGraph (Fin 4)).commonNeighbors octahedronA octahedronB
  let f : common → G.commonNeighbors a b := fun x =>
    ⟨iso x.val, iso.map_rel_iff.mpr x.property.1, iso.map_rel_iff.mpr x.property.2⟩
  have hInjective : Function.Injective f := by
    intro x y hEq
    have hVal := congrArg (fun z : G.commonNeighbors a b => z.val) hEq
    exact Subtype.ext (iso.injective (Subtype.ext hVal))
  let other : G.commonNeighbors a b := ⟨root, G.adj_symm a.property, G.adj_symm b.property⟩
  have hRoot (x : common) : other ≠ f x := fun hEq =>
    (G.ne_of_adj (iso x.val).property) (congrArg Subtype.val hEq)
  let count : Option common → G.commonNeighbors a b := fun x => x.elim other f
  have hCount : Function.Injective count := by
    intro x y hEq
    cases x <;> cases y
    · rfl
    · exact (hRoot _ hEq).elim
    · exact (hRoot _ hEq.symm).elim
    · exact congrArg some (hInjective hEq)
  have hμ : 5 ≤ μ := by
    have hSize := Fintype.card_le_of_injective count hCount
    rw [h.of_not_adj hab hNonadj, Fintype.card_option] at hSize
    exact (by decide : Fintype.card common + 1 = 5) ▸ hSize
  subst k
  subst l
  have hn : 0 < n := h.card ▸ Fintype.card_pos_iff.mpr ⟨root⟩
  obtain ⟨rfl, rfl⟩ := locallyTriangular_four_srg_order G h hn hμ
  exact ⟨rfl, rfl, rfl, rfl, by simpa only [h.card, show 8 - 1 - 6 = 1 by decide] using
    h.regular.compl⟩

/-- The order-eight locally octahedral host is the complete multipartite
graph with four parts of size two. -/
theorem locallyTriangular_four_completeEquipartite
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n k l μ : ℕ} (h : G.IsSRGWith n k l μ) (root : V)
    (iso : triangularGraph (Fin 4) ≃g G.induce (G.neighborSet root)) :
    Nonempty (G ≃g completeEquipartiteGraph 4 2) := by
  classical
  obtain ⟨hn, _, _, _, hRegular⟩ := locallyTriangular_four_recognition G h root iso
  have hMultipartite : G.IsCompleteMultipartite := by
    constructor
    intro a b c hab hbc hac
    by_cases hab' : a = b
    · exact hbc (hab' ▸ hac)
    by_cases hbc' : b = c
    · exact hab (hbc'.symm ▸ hac)
    obtain ⟨_, _, hUnique⟩ := degree_eq_one_iff_existsUnique_adj.mp (hRegular b)
    have ha : Gᶜ.Adj b a := ⟨Ne.symm hab', fun hba => hab hba.symm⟩
    have hc : Gᶜ.Adj b c := ⟨hbc', hbc⟩
    exact hac.ne ((hUnique a ha).trans (hUnique c hc).symm)
  let Q := Quotient hMultipartite.setoid
  let parts (c : Q) := {x : V // hMultipartite.setoid.r c.out x}
  let : Fintype Q := Fintype.ofFinite Q
  let (c : Q) : Fintype (parts c) := Fintype.ofFinite (parts c)
  have hPart (c : Q) : Fintype.card (parts c) = 2 := by
    let partEquiv : parts c ≃ Option (Gᶜ.neighborSet c.out) :=
      { toFun x := if hx : c.out = x.val then none else some ⟨x.val, hx, x.property⟩
        invFun := fun x => x.elim ⟨c.out, hMultipartite.setoid.refl _⟩
          (fun y => ⟨y.val, y.property.2⟩)
        left_inv := by
          intro x
          by_cases hx : c.out = x.val
          · simp [hx]
          · simp [hx]
        right_inv := by
          intro x
          cases x with
          | none => simp
          | some y => simp [y.property.1] }
    rw [Fintype.card_congr partEquiv, Fintype.card_option,
      Gᶜ.card_neighborSet_eq_degree, hRegular]
  have hTotal : Fintype.card V = Fintype.card (Sigma parts) :=
    Fintype.card_congr hMultipartite.iso.toEquiv
  rw [h.card, hn, Fintype.card_sigma] at hTotal
  simp only [hPart, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hTotal
  change 8 = Fintype.card Q * 2 at hTotal
  let partIndex : Q ≃ Fin 4 := Fintype.equivFinOfCardEq (by omega)
  let label (c : Q) : parts c ≃ Fin 2 := Fintype.equivFinOfCardEq (hPart c)
  let vertices := (Equiv.sigmaCongr partIndex label).trans (Equiv.sigmaEquivProd _ _)
  let relabel : completeMultipartiteGraph parts ≃g completeEquipartiteGraph 4 2 :=
    { toEquiv := vertices
      map_rel_iff' := by
        intro a b
        change partIndex a.1 ≠ partIndex b.1 ↔ a.1 ≠ b.1
        exact not_congr partIndex.injective.eq_iff }
  exact ⟨hMultipartite.iso.trans relabel⟩

end EPPAIII.Primitive
