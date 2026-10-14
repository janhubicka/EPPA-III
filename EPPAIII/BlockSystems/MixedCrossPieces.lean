import EPPAIII.BlockSystems.CrossBlockSizeEquation
import EPPAIII.BlockSystems.Case1UnoccupiedBound

/-!
# The two cross-edge pieces in unequal-clique Case 1

When the host has exactly two invariant blocks i,j and all
cross-block edges are mixed between selected and outside
vertices, the cross-block graph preserves the two vertex sets

    P(i,j) = (selected in i) ∪ (outside in j),
    P(j,i) = (selected in j) ∪ (outside in i).

Once the selected occupancies satisfy k_i+k_j=m and all
host blocks have size m, the first piece has 2k_i vertices
and the second 2k_j. This is the combinatorial partition
used in the final perfect-matching argument; connectivity
of the two pieces when r>=2 is a separate EPPA lemma.
-/

namespace EPPAIII.BlockSystems

/-- One of the two bipartite pieces of the actual cross-block
edge graph of the host. -/
noncomputable def mixedCrossPiece {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (i j : B) : Finset W :=
  selectedHostBlock e block i ∪ outsideHostBlock e block j

/-- Membership in a piece is exactly selected-in-i or outside-in-j. -/
theorem mem_mixedCrossPiece_iff {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (i j : B) (w : W) :
    w ∈ mixedCrossPiece e block i j ↔
      (block w = i ∧ w ∈ Set.range e) ∨
        (block w = j ∧ w ∉ Set.range e) := by
  classical
  simp only [mixedCrossPiece, Finset.mem_union,
    mem_selectedHostBlock_iff, mem_outsideHostBlock_iff]

/-- Every cross-edge starting inside one piece ends in the same
piece, provided the host has only two block labels and all
cross-edges have one selected and one outside endpoint. -/
theorem mixedCrossPiece_edge_closed {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (H : SimpleGraph W) (e : V ↪ W) (block : W → B)
    (i j : B) (hTwoLabels : ∀ b : B, b = i ∨ b = j)
    (hMixed : ∀ u v : W, (crossBlockGraph H block).Adj u v →
      (u ∈ Set.range e ∧ v ∉ Set.range e) ∨
      (u ∉ Set.range e ∧ v ∈ Set.range e)) :
    ∀ u ∈ mixedCrossPiece e block i j, ∀ v : W,
      (crossBlockGraph H block).Adj u v →
        v ∈ mixedCrossPiece e block i j := by
  intro u hu v huv
  have hPiece := (mem_mixedCrossPiece_iff e block i j u).mp hu
  have hOther := hMixed u v huv
  have hDiff : block u ≠ block v := huv.2
  apply (mem_mixedCrossPiece_iff e block i j v).mpr
  rcases hPiece with ⟨hui,huSelected⟩ | ⟨huj,huOutside⟩
  · have hvOutside : v ∉ Set.range e := by
      rcases hOther with ⟨_,h⟩ | ⟨h,_⟩
      · exact h
      · exact False.elim (h huSelected)
    rcases hTwoLabels (block v) with hvi | hvj
    · exact False.elim (hDiff (hui.trans hvi.symm))
    · exact Or.inr ⟨hvj,hvOutside⟩
  · have hvSelected : v ∈ Set.range e := by
      rcases hOther with ⟨h,_⟩ | ⟨_,h⟩
      · exact False.elim (huOutside h)
      · exact h
    rcases hTwoLabels (block v) with hvi | hvj
    · exact Or.inl ⟨hvi,hvSelected⟩
    · exact False.elim (hDiff (huj.trans hvj.symm))

/-- The first bipartite piece has exactly twice the selected
occupancy k_i when k_i+k_j=m. -/
theorem mixedCrossPiece_card_twice_selected {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B)
    (i j : B) (m : ℕ)
    (hBlockSize :
      ((Finset.univ : Finset W).filter
        (fun w => block w = j)).card = m)
    (hComplementary :
      (selectedInBlock e block i).card +
        (selectedInBlock e block j).card = m) :
    (mixedCrossPiece e block i j).card =
      2 * (selectedInBlock e block i).card := by
  classical
  have hDisjoint :
      Disjoint (selectedHostBlock e block i)
        (outsideHostBlock e block j) := by
    apply Finset.disjoint_left.mpr
    intro w hSel hOutside
    exact ((mem_outsideHostBlock_iff e block j w).mp hOutside).2
      ((mem_selectedHostBlock_iff e block i w).mp hSel).2
  have hSum := selected_outside_host_block_card e block j
  have hSi := selectedHostBlock_card e block i
  have hSj := selectedHostBlock_card e block j
  have hUnion :
      (mixedCrossPiece e block i j).card =
        (selectedHostBlock e block i).card +
          (outsideHostBlock e block j).card := by
    exact Finset.card_union_of_disjoint hDisjoint
  omega

end EPPAIII.BlockSystems
