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

/-- Each undirected internal edge contributes two oriented arcs. -/
theorem sideInternalArcs_eq_twice_sideEdges
    {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) (side : Bool) :
    sideInternalArcs H side =
      2 * (sideGraph H side).edgeFinset.card := by
  classical
  calc
    sideInternalArcs H side =
        ((Finset.univ : Finset (V × V)).filter
          (fun xy => H.Adj (side,xy.1) (side,xy.2))).card := by
      unfold sideInternalArcs
      rw [← Fintype.sum_prod_type]
      simpa using
        (Finset.sum_boole
          (p := fun xy : V × V => H.Adj (side,xy.1) (side,xy.2))
          (s := (Finset.univ : Finset (V × V))) (R := ℕ))
    _ = 2 * (sideGraph H side).edgeFinset.card := by
      simpa [sideGraph] using
        ((sideGraph H side).two_mul_card_edgeFinset).symm

/-- The row-balance identity is now an equality between the
number of undirected edges in the two induced side graphs. -/
theorem sideEdges_equal_of_balanced_rows
    {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V))
    (hRows : ∀ i : V,
      ((∑ j : V, if H.Adj (false,i) (false,j) then 1 else 0) +
       (∑ j : V, if H.Adj (false,i) (true,j) then 1 else 0)) =
      ((∑ j : V, if H.Adj (true,i) (true,j) then 1 else 0) +
       (∑ j : V, if H.Adj (true,i) (false,j) then 1 else 0))) :
    (sideGraph H false).edgeFinset.card =
      (sideGraph H true).edgeFinset.card := by
  have h := sideInternalArcs_eq_of_balanced_rows H hRows
  rw [sideInternalArcs_eq_twice_sideEdges,
      sideInternalArcs_eq_twice_sideEdges] at h
  omega

end EPPAIII.CliqueCovers
