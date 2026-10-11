import EPPAIII.CliqueCovers.Basic

/-!
# Equal internal adjacency counts for balanced halves

For a graph whose vertices are divided into two equally sized sides,
the internal adjacency counts of the two sides agree whenever the
total degree sums of the two sides agree. In particular this holds for
a regular graph. This is the arithmetic core of the equality
|E(H[B])| = |E(H[G])| used in the direct proof of Lemma 3.7.

We work first with oriented internal edges (each undirected internal
edge counted twice). A later bridge can express this using
SimpleGraph.edgeFinset of induced graphs. No EPPA or outside-clique
partition is assumed or used.

The main theorem below records the side-degree equality explicitly
as an adjacency-matrix row condition. It does not claim the separate
regularity-to-row-condition bridge.
-/

namespace EPPAIII.CliqueCovers

open Finset

/-- The number of oriented edges with both endpoints in one side. -/
noncomputable def sideInternalArcs {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) [DecidableRel H.Adj]
    (side : Bool) : ℕ :=
  ∑ i : V, ∑ j : V,
    if H.Adj (side,i) (side,j) then 1 else 0

/-- The number of oriented edges from the specified side to the other side. -/
noncomputable def sideCrossArcs {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) [DecidableRel H.Adj]
    (side : Bool) : ℕ :=
  ∑ i : V, ∑ j : V,
    if H.Adj (side,i) (!side,j) then 1 else 0

/-- Both orientations of the same cross-edge set are counted equally. -/
theorem sideCrossArcs_false_eq_true {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) [DecidableRel H.Adj] :
    sideCrossArcs H false = sideCrossArcs H true := by
  classical
  unfold sideCrossArcs
  simp only [Bool.not_false, Bool.not_true]
  calc
    (∑ i : V, ∑ j : V,
        if H.Adj (false,i) (true,j) then 1 else 0) =
      (∑ i : V, ∑ j : V,
        if H.Adj (true,j) (false,i) then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : H.Adj (false, i) (true, j)
          · simp [h, h.symm]
          · have h' : ¬ H.Adj (true, j) (false, i) := fun he => h he.symm
            simp [h, h']
    _ = (∑ j : V, ∑ i : V,
        if H.Adj (true,j) (false,i) then 1 else 0) := Finset.sum_comm

/-- If corresponding left/right vertices have equal adjacency
row sums, then both sides have equal numbers of internal oriented edges.
One can weaken the row condition to equality of the two *total*
degree sums without changing this proof. -/
theorem sideInternalArcs_eq_of_balanced_rows
    {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) [DecidableRel H.Adj]
    (hRows : ∀ i : V,
      ((∑ j : V, if H.Adj (false,i) (false,j) then 1 else 0) +
       (∑ j : V, if H.Adj (false,i) (true,j) then 1 else 0)) =
      ((∑ j : V, if H.Adj (true,i) (true,j) then 1 else 0) +
       (∑ j : V, if H.Adj (true,i) (false,j) then 1 else 0))) :
    sideInternalArcs H false = sideInternalArcs H true := by
  classical
  have hSum :
      (∑ i : V,
        ((∑ j : V, if H.Adj (false,i) (false,j) then 1 else 0) +
         (∑ j : V, if H.Adj (false,i) (true,j) then 1 else 0))) =
      (∑ i : V,
        ((∑ j : V, if H.Adj (true,i) (true,j) then 1 else 0) +
         (∑ j : V, if H.Adj (true,i) (false,j) then 1 else 0))) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hRows i
  simp only [Finset.sum_add_distrib] at hSum
  have hBalanced :
      sideInternalArcs H false + sideCrossArcs H false =
        sideInternalArcs H true + sideCrossArcs H true := by
    exact hSum
  have hCross := sideCrossArcs_false_eq_true H
  omega

end EPPAIII.CliqueCovers
