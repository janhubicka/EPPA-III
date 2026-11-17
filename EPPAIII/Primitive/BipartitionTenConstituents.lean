import EPPAIII.Primitive.EqualBipartitionModels
import EPPAIII.Primitive.RookModel
import EPPAIII.Primitive.Subconstituents
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fintype.Powerset

/-!
# Subconstituents of the order-126 bipartition host

For the bipartition of ten points into two five-sets, swapping one point
of each part gives the 25 local vertices and their rook graph. The
100-vertex nonlocal graph has adjacent pairs of different codegrees.
-/

namespace EPPAIII.Primitive

private def bipartitionTenPart : Finset (Fin 10) := {0, 1, 2, 3, 4}

def bipartitionTenRoot : EqualBipartitionVertex 4 :=
  ⟨bipartitionTenPart, by decide⟩

private abbrev LocalVertex := (equalBipartitionGraph 4).neighborSet bipartitionTenRoot

private abbrev NonlocalVertex :=
  {x : EqualBipartitionVertex 4 // bipartitionTenRoot ≠ x ∧
    ¬ (equalBipartitionGraph 4).Adj bipartitionTenRoot x}

private def swapPart (p : Fin 5 × Fin 5) : Finset (Fin 10) :=
  let exchanged := insert (⟨5 + p.2.val, by omega⟩ : Fin 10)
    (bipartitionTenPart.erase ⟨p.1.val, by omega⟩)
  if (0 : Fin 10) ∈ exchanged then exchanged else exchangedᶜ

private theorem swapPart_valid :
    ∀ p : Fin 5 × Fin 5, (swapPart p).card = 5 ∧ (0 : Fin 10) ∈ swapPart p := by
  decide

private def swapVertex (p : Fin 5 × Fin 5) : EqualBipartitionVertex 4 :=
  ⟨swapPart p, swapPart_valid p⟩

private theorem swapVertex_neighbor :
    ∀ p, (equalBipartitionGraph 4).Adj bipartitionTenRoot (swapVertex p) := by
  decide

private def swapNeighbor (p : Fin 5 × Fin 5) : LocalVertex :=
  ⟨swapVertex p, swapVertex_neighbor p⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem swapNeighbor_bijective : Function.Bijective swapNeighbor := by
  decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem swapNeighbor_adjacency :
    ∀ p q, (rookGraph 5).Adj p q ↔
      (localGraph (equalBipartitionGraph 4) bipartitionTenRoot).Adj
        (swapNeighbor p) (swapNeighbor q) := by
  change ∀ p q : Fin 5 × Fin 5, (p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)) ↔
    (equalBipartitionGraph 4).Adj (swapVertex p) (swapVertex q)
  decide

/-- The local graph at the indicated root is the 5-by-5 rook graph. -/
noncomputable def bipartitionTenRookIso :
    rookGraph 5 ≃g localGraph (equalBipartitionGraph 4) bipartitionTenRoot where
  toEquiv := Equiv.ofBijective swapNeighbor swapNeighbor_bijective
  map_rel_iff' := by
    intro p q
    exact (swapNeighbor_adjacency p q).symm

private def nonlocalA : NonlocalVertex := ⟨⟨{0, 1, 2, 5, 6}, by decide⟩, by decide⟩
private def nonlocalB : NonlocalVertex := ⟨⟨{0, 1, 2, 5, 7}, by decide⟩, by decide⟩
private def nonlocalC : NonlocalVertex := ⟨⟨{0, 1, 5, 6, 7}, by decide⟩, by decide⟩
private def nonlocalD : NonlocalVertex := ⟨⟨{0, 1, 2, 7, 8}, by decide⟩, by decide⟩

private abbrev secondGraph := nonlocalGraph (equalBipartitionGraph 4) bipartitionTenRoot

instance : DecidableRel secondGraph.Adj := fun a b =>
  inferInstanceAs (Decidable ((equalBipartitionGraph 4).Adj a.val b.val))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bipartitionTen_order : Fintype.card (EqualBipartitionVertex 4) = 126 := by decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bipartitionTenNonlocal_order : Fintype.card NonlocalVertex = 100 := by decide

theorem bipartitionTenNonlocal_not_degenerate : secondGraph ≠ ⊤ ∧ secondGraph ≠ ⊥ := by
  have hAD : ¬ secondGraph.Adj nonlocalA nonlocalD := by decide
  have hAB : secondGraph.Adj nonlocalA nonlocalB := by decide
  constructor
  · intro h
    exact hAD (h.symm ▸ (show (⊤ : SimpleGraph NonlocalVertex).Adj nonlocalA nonlocalD by decide))
  · intro h
    exact (h ▸ hAB : (⊥ : SimpleGraph NonlocalVertex).Adj nonlocalA nonlocalB)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem bipartitionTenNonlocal_not_srg {n k l m : ℕ} :
    ¬ secondGraph.IsSRGWith n k l m := by
  intro h
  have hAB : secondGraph.Adj nonlocalA nonlocalB := by decide
  have hAC : secondGraph.Adj nonlocalA nonlocalC := by decide
  have hCodegAB : Fintype.card (secondGraph.commonNeighbors nonlocalA nonlocalB) = 6 := by decide
  have hCodegAC : Fintype.card (secondGraph.commonNeighbors nonlocalA nonlocalC) = 8 := by decide
  exact (by decide : (6 : ℕ) ≠ 8)
    (hCodegAB.symm.trans ((h.of_adj _ _ hAB).trans ((h.of_adj _ _ hAC).symm.trans hCodegAC)))

end EPPAIII.Primitive
