import EPPAIII.BlockSystems.BipartiteDoubleCount
import EPPAIII.BlockSystems.CrossBlockNeighbourCounts
import EPPAIII.BlockSystems.OccupiedBlockMajority
import EPPAIII.BlockSystems.Claim314CrossEdges

/-!
# The complementary selected-block size equation of Lemma 3.12

Let the selected copy G have all its edges within invariant
host blocks, and suppose there are no edges between outside
vertices in distinct blocks. Assume every vertex of the host
has the same positive number r of neighbours in each *other*
block.

For distinct blocks i,j, the cross edges between the selected
vertices of block i and the outside vertices of block j form
an r-regular bipartite graph on both sides. Double counting
therefore gives k_i = m-k_j, where k_i is the selected
occupancy and m is the uniform block size.

This is the missing pairwise equation of Claim 3.15. No EPPA
or transitivity is silently assumed: their output hypotheses
are recorded explicitly, and the next integration theorem will
supply them from the already verified action lemmas.
-/

namespace EPPAIII.BlockSystems

/-- Selected host vertices in block i, with actual host labels. -/
noncomputable def selectedHostBlock {V W B : Type*}
    [Fintype V] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (i : B) : Finset W :=
  (selectedInBlock e block i).image e

theorem mem_selectedHostBlock_iff {V W B : Type*}
    [Fintype V] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (i : B) (w : W) :
    w ∈ selectedHostBlock e block i ↔
      block w = i ∧ w ∈ Set.range e := by
  classical
  constructor
  · intro h
    obtain ⟨x,hx,hxw⟩ := Finset.mem_image.mp h
    have hblock : block (e x) = i := (Finset.mem_filter.mp hx).2
    refine ⟨?_, ⟨x,hxw⟩⟩
    rw [← hxw]
    exact hblock
  · rintro ⟨hblock,⟨x,hxw⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨x,?_,hxw⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [hxw]
    exact hblock

theorem selectedHostBlock_card {V W B : Type*}
    [Fintype V] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (i : B) :
    (selectedHostBlock e block i).card =
      (selectedInBlock e block i).card := by
  classical
  exact Finset.card_image_of_injective _ e.injective

/-- The vertices of a host block not in the selected copy.
Defining it as a finite set difference makes the
block-cardinality identity immediate. -/
noncomputable def outsideHostBlock {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (i : B) : Finset W :=
  ((Finset.univ : Finset W).filter (fun w => block w = i)) \
    selectedHostBlock e block i

theorem mem_outsideHostBlock_iff {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (i : B) (w : W) :
    w ∈ outsideHostBlock e block i ↔
      block w = i ∧ w ∉ Set.range e := by
  classical
  simp only [outsideHostBlock, Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hblock,hnot⟩
    refine ⟨hblock,?_⟩
    intro hrange
    exact hnot ((mem_selectedHostBlock_iff e block i w).mpr
      ⟨hblock,hrange⟩)
  · rintro ⟨hblock,hnot⟩
    refine ⟨hblock,?_⟩
    intro hsel
    exact hnot ((mem_selectedHostBlock_iff e block i w).mp hsel).2

/-- Each host block splits, without overlap, into selected
and outside parts. -/
theorem selected_outside_host_block_card {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (i : B) :
    (selectedHostBlock e block i).card +
      (outsideHostBlock e block i).card =
        ((Finset.univ : Finset W).filter (fun w => block w = i)).card := by
  classical
  let F : Finset W :=
    (Finset.univ : Finset W).filter (fun w => block w = i)
  let S : Finset W := selectedHostBlock e block i
  have hSub : S ⊆ F := by
    intro w hw
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,((mem_selectedHostBlock_iff e block i w).mp hw).1⟩
  have hCard : (outsideHostBlock e block i).card = F.card - S.card := by
    change (F \ S).card = F.card - S.card
    exact Finset.card_sdiff_of_subset hSub
  have hBound : S.card ≤ F.card := Finset.card_le_card hSub
  change S.card + (outsideHostBlock e block i).card = F.card
  omega

/-- A selected vertex in block i can only be joined to outside
vertices in a distinct block j. -/
theorem selected_cross_neighbours_outside {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (he : IsInducedGraphEmbedding G H e)
    (block : W → B)
    (hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y))
    (i j : B) (hij : i ≠ j)
    (x : V) (hxi : block (e x) = i) :
    ((outsideHostBlock e block j).filter
      (fun v => H.Adj (e x) v)) =
        ((Finset.univ : Finset W).filter
          (fun v => block v = j ∧ H.Adj (e x) v)) := by
  classical
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_outsideHostBlock_iff]
  constructor
  · rintro ⟨⟨hvj,_⟩,hadj⟩
    exact ⟨hvj,hadj⟩
  · rintro ⟨hvj,hadj⟩
    refine ⟨⟨hvj,?_⟩,hadj⟩
    rintro ⟨y,hy⟩
    have hAdj : H.Adj (e x) (e y) := by simpa only [hy] using hadj
    have hG : G.Adj x y := (he x y).mpr hAdj
    have hSame : block (e x) = block (e y) :=
      hSelectedInside x y hG
    have hY : block (e y) = j := by rw [hy]; exact hvj
    exact hij ((hxi.symm.trans hSame).trans hY)

/-- Outside vertices in block j can only be joined to selected
vertices in a distinct block i. -/
theorem outside_cross_neighbours_selected {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (block : W → B)
    (hOutsideInside : ∀ u v : W, u ∉ Set.range e →
      v ∉ Set.range e → H.Adj u v → block u = block v)
    (i j : B) (hij : i ≠ j)
    (v : W) (hvj : block v = j) (hvOutside : v ∉ Set.range e) :
    ((selectedHostBlock e block i).filter (fun w => H.Adj v w)) =
      ((Finset.univ : Finset W).filter
        (fun w => block w = i ∧ H.Adj v w)) := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_selectedHostBlock_iff]
  constructor
  · rintro ⟨⟨hwi,_⟩,hadj⟩
    exact ⟨hwi,hadj⟩
  · rintro ⟨hwi,hadj⟩
    refine ⟨⟨hwi,?_⟩,hadj⟩
    by_contra hwOutside
    have hSame : block v = block w :=
      hOutsideInside v w hvOutside hwOutside hadj
    exact hij (hwi.symm.trans (hSame.symm.trans hvj))

/-- With a positive common cross-block degree r and the mixed
cross-block edge condition, the selected part of block i has
as many vertices as the outside part of block j (i ≠ j). -/
theorem selected_eq_outside_cross_card {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (he : IsInducedGraphEmbedding G H e)
    (block : W → B)
    (hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y))
    (hOutsideInside : ∀ u v : W, u ∉ Set.range e →
      v ∉ Set.range e → H.Adj u v → block u = block v)
    (r : ℕ) (hr : 0 < r)
    (hUniformCross : ∀ u : W, ∀ j : B, block u ≠ j →
      neighboursInBlock H block u j = r)
    (i j : B) (hij : i ≠ j) :
    (selectedInBlock e block i).card =
      (outsideHostBlock e block j).card := by
  classical
  let S : Finset W := selectedHostBlock e block i
  let T : Finset W := outsideHostBlock e block j
  have hRows : ∀ u ∈ S,
      (T.filter (fun v => H.Adj u v)).card = r := by
    intro u hu
    obtain ⟨x,hx,hxu⟩ := Finset.mem_image.mp hu
    have hxi : block (e x) = i := (Finset.mem_filter.mp hx).2
    have hRow :
        (T.filter (fun v => H.Adj (e x) v)).card = r := by
      calc
        (T.filter (fun v => H.Adj (e x) v)).card =
            (((Finset.univ : Finset W).filter
              (fun v => block v = j ∧ H.Adj (e x) v))).card :=
          congrArg Finset.card
            (selected_cross_neighbours_outside
              G H e he block hSelectedInside i j hij x hxi)
        _ = neighboursInBlock H block (e x) j := rfl
        _ = r := hUniformCross (e x) j (by rw [hxi]; exact hij)
    simpa only [hxu] using hRow
  have hColumns : ∀ v ∈ T,
      (S.filter (fun u => H.Adj v u)).card = r := by
    intro v hv
    have hvInfo := (mem_outsideHostBlock_iff e block j v).mp hv
    calc
      (S.filter (fun u => H.Adj v u)).card =
          (((Finset.univ : Finset W).filter
            (fun u => block u = i ∧ H.Adj v u))).card :=
        congrArg Finset.card
          (outside_cross_neighbours_selected
            H e block hOutsideInside i j hij v hvInfo.1 hvInfo.2)
      _ = neighboursInBlock H block v i := rfl
      _ = r := hUniformCross v i (by rw [hvInfo.1]; exact hij.symm)
  have hEq : S.card = T.card :=
    symmetric_bipartite_regular_card_eq H S T r hr hRows hColumns
  calc
    (selectedInBlock e block i).card = S.card :=
      (selectedHostBlock_card e block i).symm
    _ = T.card := hEq
    _ = (outsideHostBlock e block j).card := rfl

/-- Double-counting inter-block edges produces the precise
pairwise complementary selected occupancy equation
k_i+k_j=m of Claim 3.15. -/
theorem selected_occupied_pairwise_complementary {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (he : IsInducedGraphEmbedding G H e)
    (block : W → B)
    (hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y))
    (hOutsideInside : ∀ u v : W, u ∉ Set.range e →
      v ∉ Set.range e → H.Adj u v → block u = block v)
    (m : ℕ)
    (hUniformSize : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card = m)
    (r : ℕ) (hr : 0 < r)
    (hUniformCross : ∀ u : W, ∀ j : B, block u ≠ j →
      neighboursInBlock H block u j = r)
    (i j : B) (hij : i ≠ j) :
    (selectedInBlock e block i).card +
      (selectedInBlock e block j).card = m := by
  have hBetween :=
    selected_eq_outside_cross_card
      G H e he block hSelectedInside hOutsideInside
      r hr hUniformCross i j hij
  have hSplit :=
    selected_outside_host_block_card e block j
  have hJSize := hUniformSize j
  have hJCard := selectedHostBlock_card e block j
  omega

end EPPAIII.BlockSystems
