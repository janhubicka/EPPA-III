import EPPAIII.CliqueCovers.TwoHalvesArcCount

/-!
# Relating oriented internal arcs to ordinary undirected edges

The two-half adjacency-row lemma works with oriented edges because
the arithmetic then has no division by two. Here we turn this into a
precise statement about the edgeFinset of each actual induced-side graph.

The graph on side b is obtained by pulling back H under
  i ↦ (b,i).
This is isomorphic to the induced graph on the corresponding half.
-/

namespace EPPAIII.CliqueCovers

open Finset

/-- The induced graph on one labelled side of Bool × V. -/
def sideGraph {V : Type*}
    (H : SimpleGraph (Bool × V)) (side : Bool) : SimpleGraph V :=
  H.comap (fun i => (side,i))

/-- The number of undirected edges within one side, with a classical
finite edge-set instance kept inside the definition rather than
leaking into the theorem statement. -/
noncomputable def sideEdgeCount {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) (side : Bool) : ℕ := by
  classical
  exact (sideGraph H side).edgeFinset.card

/-- Each undirected internal edge contributes two oriented arcs. -/
theorem sideInternalArcs_eq_twice_sideEdges
    {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) [DecidableRel H.Adj] (side : Bool) :
    sideInternalArcs H side =
      2 * sideEdgeCount H side := by
  classical
  calc
    sideInternalArcs H side =
        ((Finset.univ : Finset (V × V)).filter
          (fun xy => H.Adj (side,xy.1) (side,xy.2))).card := by
      unfold sideInternalArcs
      simpa [Fintype.sum_prod_type] using
        (Finset.sum_boole
          (p := fun xy : V × V => H.Adj (side,xy.1) (side,xy.2))
          (s := (Finset.univ : Finset (V × V))) (R := ℕ))
    _ = 2 * sideEdgeCount H side := by
      simpa [sideGraph, sideEdgeCount] using
        ((sideGraph H side).two_mul_card_edgeFinset).symm

/-- The row-balance identity is now an equality between the
number of undirected edges in the two induced side graphs. -/
theorem sideEdges_equal_of_balanced_rows
    {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) [DecidableRel H.Adj]
    (hRows : ∀ i : V,
      ((∑ j : V, if H.Adj (false,i) (false,j) then 1 else 0) +
       (∑ j : V, if H.Adj (false,i) (true,j) then 1 else 0)) =
      ((∑ j : V, if H.Adj (true,i) (true,j) then 1 else 0) +
       (∑ j : V, if H.Adj (true,i) (false,j) then 1 else 0))) :
    sideEdgeCount H false =
      sideEdgeCount H true := by
  have h := sideInternalArcs_eq_of_balanced_rows H hRows
  rw [sideInternalArcs_eq_twice_sideEdges,
      sideInternalArcs_eq_twice_sideEdges] at h
  omega

end EPPAIII.CliqueCovers
