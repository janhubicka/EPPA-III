import EPPAIII.BlockSystems.SharedCrossNeighbours
import EPPAIII.BlockSystems.UniformCrossBlockDegrees
import EPPAIII.BlockSystems.UnequalCliqueBaseBlocks
import EPPAIII.BlockSystems.Claim314CrossEdges

/-!
# When r >= 2, every selected pair in a clique shares a cross-neighbour

Suppose the actual EPPA host has an invariant partition and
all selected edges lie inside blocks. Its true two-point EPPA
action transports the property of two selected vertices having
a common neighbour in the cross-block graph.

Choose an outside vertex z in block j. If its cross-degree
into a different block i is r >= 2, two distinct vertices of
block i are adjacent to z. Claim 3.14 makes those two
neighbours selected vertices, and the selected block relation
makes them adjacent in G.

Two-point EPPA now transports their shared cross-neighbour
to every ordered pair of distinct selected vertices in block i.
This is the needed local EPPA ingredient for connectedness of
the bipartite pieces in the perfect-matching argument.
-/

namespace EPPAIII.BlockSystems

/-- Every pair of distinct selected vertices in an occupied
clique block i has a common neighbour in the *cross-block*
graph when any outside vertex of another block j has
cross-degree at least two into i. -/
theorem eppa_shared_cross_neighbour_of_degree_two
    {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y)
    (hOutsideInside : ∀ u v : W,
      u ∉ Set.range e → v ∉ Set.range e →
      H.Adj u v → block u = block v)
    (i j : B) (hij : i ≠ j)
    (z : W) (hzj : block z = j) (hzOutside : z ∉ Set.range e)
    (r : ℕ) (hr : 2 ≤ r)
    (hDegree : neighboursInBlock H block z i = r) :
    ∀ x y : V,
      block (e x) = i → block (e y) = i → x ≠ y →
      HasCommonNeighbour (crossBlockGraph H block) (e x) (e y) := by
  classical
  let N : Finset W := (Finset.univ : Finset W).filter
    (fun w => block w = i ∧ H.Adj z w)
  have hNcard : N.card = r := hDegree
  have hTwo : 1 < N.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hTwo
  have haParts : block a = i ∧ H.Adj z a :=
    (Finset.mem_filter.mp ha).2
  have hbParts : block b = i ∧ H.Adj z b :=
    (Finset.mem_filter.mp hb).2
  have hSelected (w : W) (hw : block w = i)
      (hzw : H.Adj z w) : w ∈ Set.range e := by
    by_contra hwOut
    have hSameBlocks := hOutsideInside z w hzOutside hwOut hzw
    exact hij (hw.symm.trans (hSameBlocks.symm.trans hzj))
  obtain ⟨x₀,hx₀⟩ := hSelected a haParts.1 haParts.2
  obtain ⟨y₀,hy₀⟩ := hSelected b hbParts.1 hbParts.2
  have hxy₀ : x₀ ≠ y₀ := by
    intro heq
    apply hab
    calc
      a = e x₀ := hx₀.symm
      _ = e y₀ := by rw [heq]
      _ = b := hy₀
  have hBlock₀ : block (e x₀) = block (e y₀) := by
    calc
      block (e x₀) = block a := congrArg block hx₀
      _ = i := haParts.1
      _ = block b := hbParts.1.symm
      _ = block (e y₀) := congrArg block hy₀.symm
  have hAdj₀ : G.Adj x₀ y₀ := by
    rcases (hSame x₀ y₀).mp hBlock₀ with heq | hadj
    · exact False.elim (hxy₀ heq)
    · exact hadj
  have hCommon₀ :
      HasCommonNeighbour (crossBlockGraph H block) (e x₀) (e y₀) := by
    refine ⟨z,?_,?_⟩
    · refine ⟨?_,?_⟩
      · simpa [←hx₀] using haParts.2.symm
      · calc
          block (e x₀) = i := by rw [hx₀]; exact haParts.1
          _ ≠ j := hij
          _ = block z := hzj.symm
    · refine ⟨?_,?_⟩
      · simpa [←hy₀] using hbParts.2.symm
      · calc
          block (e y₀) = i := by rw [hy₀]; exact hbParts.1
          _ ≠ j := hij
          _ = block z := hzj.symm
  intro x y hxi hyi hxy
  have hTargetAdj : G.Adj x y := by
    rcases (hSame x y).mp (hxi.trans hyi.symm) with heq | hadj
    · exact False.elim (hxy heq)
    · exact hadj
  have hType : G.Adj x₀ y₀ ↔ G.Adj x y :=
    ⟨fun _ => hTargetAdj,fun _ => hAdj₀⟩
  exact (eppa_common_cross_neighbour_pair_invariant
      G H e heppa block hBlocks x₀ y₀ x y hxy₀ hxy hType).mp
    hCommon₀

end EPPAIII.BlockSystems
