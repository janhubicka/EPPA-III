import EPPAIII.CliqueCovers.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! # Induced five-cycles in generalized clique covers -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem side_and_block_of_distinguishes {s t : ℕ} (X : CrossType) (Y : Bool)
    {a b u : CoverVertex s t} (hSide : a.1 = b.1) (hBlock : a.2.1 = b.2.1)
    (hu : u ≠ b) (hua : (coverGraph s t X Y).Adj u a)
    (hub : ¬ (coverGraph s t X Y).Adj u b) :
    u.1 ≠ a.1 ∧ u.2.1 = a.2.1 := by
  change coverAdj X Y u a at hua
  change ¬ coverAdj X Y u b at hub
  have hOpp : u.1 ≠ a.1 := by
    intro hSame
    have hIndex := (hua.resolve_right (fun h => h.1 hSame)).2.1.trans hBlock
    have hSide' := hSame.trans hSide
    have hCoordinate : u.2.2 ≠ b.2.2 := fun h => hu (Prod.ext hSide' (Prod.ext hIndex h))
    exact hub (Or.inl ⟨hSide', hIndex, hCoordinate⟩)
  refine ⟨hOpp, ?_⟩
  by_contra hDifferent
  have hOtherSide : u.1 ≠ b.1 := fun h => hOpp (h.trans hSide.symm)
  have hOtherBlock : u.2.1 ≠ b.2.1 := fun h => hDifferent (h.trans hBlock.symm)
  have hY : Y = true := by
    simpa only [hDifferent, ite_false] using (hua.resolve_left (fun h => hOpp h.1)).2
  exact hub (Or.inr ⟨hOtherSide, by simpa only [hOtherBlock, ite_false] using hY⟩)

private theorem five_cycle_has_same_side_edge (side : Fin 5 → Bool) :
    ∃ i, side i = side (i + 1) := by
  have hOdd : ∀ a b c d e : Bool, a = b ∨ b = c ∨ c = d ∨ d = e ∨ e = a := by decide
  rcases hOdd (side 0) (side 1) (side 2) (side 3) (side 4) with h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩

/-- Every generalized clique cover is induced-five-cycle-free. -/
theorem no_induced_five_cycle_in_cover {s t : ℕ} (X : CrossType) (Y : Bool) :
    IsEmpty (cycleGraph 5 ↪g coverGraph s t X Y) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨i, hSide⟩ := five_cycle_has_same_side_edge (fun j => (f j).1)
  have hab : (coverGraph s t X Y).Adj (f i) (f (i + 1)) :=
    f.map_adj_iff.mpr ((show ∀ j : Fin 5, (cycleGraph 5).Adj j (j + 1) by decide) i)
  have hpA : (coverGraph s t X Y).Adj (f (i + 4)) (f i) :=
    f.map_adj_iff.mpr ((show ∀ j : Fin 5, (cycleGraph 5).Adj (j + 4) j by decide) i)
  have hqB : (coverGraph s t X Y).Adj (f (i + 2)) (f (i + 1)) :=
    f.map_adj_iff.mpr ((show ∀ j : Fin 5, (cycleGraph 5).Adj (j + 2) (j + 1) by decide) i)
  have hpB : ¬ (coverGraph s t X Y).Adj (f (i + 4)) (f (i + 1)) :=
    fun h => (show ∀ j : Fin 5, ¬ (cycleGraph 5).Adj (j + 4) (j + 1) by decide) i
      (f.map_adj_iff.mp h)
  have hqA : ¬ (coverGraph s t X Y).Adj (f (i + 2)) (f i) :=
    fun h => (show ∀ j : Fin 5, ¬ (cycleGraph 5).Adj (j + 2) j by decide) i
      (f.map_adj_iff.mp h)
  have hpq : ¬ (coverGraph s t X Y).Adj (f (i + 4)) (f (i + 2)) :=
    fun h => (show ∀ j : Fin 5, ¬ (cycleGraph 5).Adj (j + 4) (j + 2) by decide) i
      (f.map_adj_iff.mp h)
  have hBlock : (f i).2.1 = (f (i + 1)).2.1 :=
    (hab.resolve_right (fun h => h.1 hSide)).2.1
  obtain ⟨hpSide, hpBlock⟩ :=
    side_and_block_of_distinguishes X Y hSide hBlock
      (f.injective.ne ((show ∀ j : Fin 5, j + 4 ≠ j + 1 by decide) i)) hpA hpB
  obtain ⟨hqSide, hqBlock⟩ :=
    side_and_block_of_distinguishes X Y hSide.symm hBlock.symm
      (f.injective.ne ((show ∀ j : Fin 5, j + 2 ≠ j by decide) i)) hqB hqA
  have hSameSide : (f (i + 4)).1 = (f (i + 2)).1 := by
    have hqSide' : (f (i + 2)).1 ≠ (f i).1 := fun h => hqSide (h.trans hSide)
    exact (show ∀ x y z : Bool, x ≠ z → y ≠ z → x = y by decide) _ _ _ hpSide hqSide'
  have hSameBlock : (f (i + 4)).2.1 = (f (i + 2)).2.1 :=
    hpBlock.trans (hBlock.trans hqBlock.symm)
  have hDifferentCoordinates : (f (i + 4)).2.2 ≠ (f (i + 2)).2.2 := by
    intro h
    exact (show ∀ j : Fin 5, j + 4 ≠ j + 2 by decide) i
      (f.injective (Prod.ext hSameSide (Prod.ext hSameBlock h)))
  exact hpq (Or.inl ⟨hSameSide, hSameBlock, hDifferentCoordinates⟩)

private def cycleFive_complEmbedding : cycleGraph 5 ↪g (cycleGraph 5)ᶜ where
  toFun i := i + i
  inj' := by
    have h : ∀ i j : Fin 5, i + i = j + j → i = j := by decide
    exact fun {i j} => h i j
  map_rel_iff' := by
    have h : ∀ i j : Fin 5,
        (i + i ≠ j + j ∧ ¬(cycleGraph 5).Adj (i + i) (j + j)) ↔
          (cycleGraph 5).Adj i j := by decide
    exact fun {i j} => h i j

/-- Complements of generalized clique covers are also induced-five-cycle-free. -/
theorem no_induced_five_cycle_in_compl_cover {s t : ℕ} (X : CrossType) (Y : Bool) :
    IsEmpty (cycleGraph 5 ↪g (coverGraph s t X Y)ᶜ) := by
  refine ⟨fun f => (no_induced_five_cycle_in_cover (s := s) (t := t) X Y).false ?_⟩
  have f' : (cycleGraph 5)ᶜ ↪g coverGraph s t X Y := by
    simpa only [compl_compl] using Embedding.complEquiv f
  exact f'.comp cycleFive_complEmbedding

/-- Equal-clique unions are induced-five-cycle-free. -/
theorem no_induced_five_cycle_in_clique_union (s t : ℕ) :
    IsEmpty (cycleGraph 5 ↪g cliqueUnion s t) := by
  refine ⟨fun f => ?_⟩
  have h01 : (cliqueUnion s t).Adj (f 0) (f 1) :=
    f.map_adj_iff.mpr (by decide)
  have h12 : (cliqueUnion s t).Adj (f 1) (f 2) :=
    f.map_adj_iff.mpr (by decide)
  have h02 : (f 0).1 = (f 2).1 := h01.1.trans h12.1
  have hCoord : (f 0).2 ≠ (f 2).2 := fun h =>
    (show (0 : Fin 5) ≠ 2 by decide) (f.injective (Prod.ext h02 h))
  exact (show ¬ (cycleGraph 5).Adj 0 2 by decide) (f.map_adj_iff.mp ⟨h02, hCoord⟩)

/-- Complements of equal-clique unions are induced-five-cycle-free. -/
theorem no_induced_five_cycle_in_compl_clique_union (s t : ℕ) :
    IsEmpty (cycleGraph 5 ↪g (cliqueUnion s t)ᶜ) := by
  refine ⟨fun f => (no_induced_five_cycle_in_clique_union s t).false ?_⟩
  have f' : (cycleGraph 5)ᶜ ↪g cliqueUnion s t := by
    simpa only [compl_compl] using Embedding.complEquiv f
  exact f'.comp cycleFive_complEmbedding

/-- An induced five-cycle excludes both orientations of equal-clique unions. -/
theorem no_clique_union_or_compl_of_induced_five_cycle {V : Type*} {G : SimpleGraph V}
    (f : cycleGraph 5 ↪g G) (s t : ℕ) :
    IsEmpty (G ≃g cliqueUnion s t) ∧ IsEmpty (G ≃g (cliqueUnion s t)ᶜ) := by
  exact ⟨⟨fun φ => (no_induced_five_cycle_in_clique_union s t).false (φ.toEmbedding.comp f)⟩,
    ⟨fun φ => (no_induced_five_cycle_in_compl_clique_union s t).false (φ.toEmbedding.comp f)⟩⟩

/-- An induced five-cycle certifies that a graph has neither orientation of a
generalized clique cover. -/
theorem no_cover_or_compl_of_induced_five_cycle {V : Type*} {G : SimpleGraph V}
    (f : cycleGraph 5 ↪g G) (s t : ℕ) (X : CrossType) (Y : Bool) :
    IsEmpty (G ≃g coverGraph s t X Y) ∧ IsEmpty (G ≃g (coverGraph s t X Y)ᶜ) := by
  constructor
  · exact ⟨fun φ =>
      (no_induced_five_cycle_in_cover (s := s) (t := t) X Y).false (φ.toEmbedding.comp f)⟩
  · exact ⟨fun φ =>
      (no_induced_five_cycle_in_compl_cover (s := s) (t := t) X Y).false (φ.toEmbedding.comp f)⟩

end EPPAIII.Primitive
