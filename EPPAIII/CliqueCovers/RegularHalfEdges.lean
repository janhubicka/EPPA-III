import EPPAIII.CliqueCovers.SideGraphCount

/-!
# Equal edge counts from ordinary regularity of the host graph

This module removes the artificial "balanced rows" hypothesis from
the two-half edge-count result. For a regular graph on Bool × V,
the degree of (b,i) is exactly its number of neighbours on the
false side plus its number on the true side. Equality of total
degrees therefore implies equal edge counts in the induced halves.

No EPPA or clique partition assumption is used. The final transport
from an arbitrary host vertex type W with a chosen half-size embedding
to Bool × V is a separate (finite equivalence) obligation.
-/

namespace EPPAIII.CliqueCovers

open Finset

/-- A graph vertex's degree splits exactly into the two labelled sides. -/
theorem sideDegree_eq_two_row_sums {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) [DecidableRel H.Adj]
    (side : Bool) (i : V) :
    H.degree (side,i) =
      (∑ j : V, if H.Adj (side,i) (false,j) then 1 else 0) +
      (∑ j : V, if H.Adj (side,i) (true,j) then 1 else 0) := by
  classical
  calc
    H.degree (side,i) =
      ((Finset.univ : Finset (Bool × V)).filter
        (fun z => H.Adj (side,i) z)).card := by
      rw [SimpleGraph.degree, H.neighborFinset_eq_filter]
    _ = (∑ z : Bool × V, if H.Adj (side,i) z then 1 else 0) := by
      simpa using
        (Finset.sum_boole
          (p := fun z : Bool × V => H.Adj (side,i) z)
          (s := (Finset.univ : Finset (Bool × V))) (R := ℕ)).symm
    _ = (∑ c : Bool, ∑ j : V,
          if H.Adj (side,i) (c,j) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
    _ = (∑ j : V, if H.Adj (side,i) (false,j) then 1 else 0) +
        (∑ j : V, if H.Adj (side,i) (true,j) then 1 else 0) := by
      simp [Fintype.sum_bool, Nat.add_comm]

/-- Pairwise equality of corresponding graph degrees implies the
same number of undirected edges in the two induced halves. -/
theorem sideEdges_equal_of_equal_degrees
    {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V))
    (hDegree : ∀ i : V, H.degree (false,i) = H.degree (true,i)) :
    (sideGraph H false).edgeFinset.card =
      (sideGraph H true).edgeFinset.card := by
  classical
  apply sideEdges_equal_of_balanced_rows H
  intro i
  have hl := sideDegree_eq_two_row_sums H false i
  have hr := sideDegree_eq_two_row_sums H true i
  have heq := hDegree i
  omega

/-- Regularity of the whole host is sufficient for the required
induced-half edge-count equality. -/
theorem sideEdges_equal_of_regular_graph
    {V : Type*} [Fintype V]
    (H : SimpleGraph (Bool × V)) (d : ℕ)
    (hReg : H.IsRegularOfDegree d) :
    (sideGraph H false).edgeFinset.card =
      (sideGraph H true).edgeFinset.card := by
  apply sideEdges_equal_of_equal_degrees H
  intro i
  exact (hReg (false,i)).trans (hReg (true,i)).symm

end EPPAIII.CliqueCovers
