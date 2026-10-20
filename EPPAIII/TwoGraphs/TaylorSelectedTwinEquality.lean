import EPPAIII.TwoGraphs.TaylorQuotientPositive
import EPPAIII.TwoGraphs.OccupiedTwinFibreCount

/-!
# Equality of true-twin quotient counts in the first case

The positive-degree quotient independence bound and the
finite occupied-fibre capacity bound together force equality.
This is the numerical heart of Section 5 fibre rigidity:
if some selected edge is a true-twin edge, the selected
vertices occupy exactly half the quotient classes and their
total number equals t times the occupied class count.

Unlike the original manuscript's proof, no exact quotient
degree m-1 and no parity argument for the total quotient
order are required. All assumptions are on the actual EPPA
embedding and vertex-transitive host.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- In the selected true-twin edge case of a transitive Taylor
EPPA witness with a nontrivial two-graph, both finite quotient
inequalities become equalities. -/
theorem taylor_selected_twin_occupied_equalities
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    [Fintype (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (closedTwinQuotientGraph (taylorPairGraph G)).Adj]
    (heppa : IsEPPAEmbedding G
      (taylorPairGraph G) (EPPAIII.DoubleCover.bottomEmbedding V))
    (hTrans : HasTransitiveGraphAutomorphisms (taylorPairGraph G))
    (hEven : ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EvenTriple G x y z)
    (x y : V) (hXY : G.Adj x y)
    (hTwin : SameClosedNeighbourhood
      (taylorPairGraph G) (false,x) (false,y)) :
    let H := taylorPairGraph G
    let Q := ClosedTwinQuotient H
    let t := (closedTwinClass H (false,x)).card
    let I : Finset Q :=
      (Finset.univ : Finset V).image
        (fun v => (Quotient.mk (closedTwinSetoid H) (false,v) : Q))
    Fintype.card V = I.card * t ∧
      Fintype.card Q = 2 * I.card := by
  classical
  let H := taylorPairGraph G
  let Q := ClosedTwinQuotient H
  let t := (closedTwinClass H (false,x)).card
  let I : Finset Q :=
    (Finset.univ : Finset V).image
      (fun v => (Quotient.mk (closedTwinSetoid H) (false,v) : Q))
  change Fintype.card V = I.card * t ∧
    Fintype.card Q = 2 * I.card
  have hUniform (w : Bool × V) :
      (closedTwinClass H w).card = t :=
    closedTwinClass_card_of_vertex_transitive
      H hTrans w (false,x)
  have hClassSelf : (false,x) ∈ closedTwinClass H (false,x) := by
    simp [closedTwinClass, SameClosedNeighbourhood]
  have ht : 0 < t :=
    Finset.card_pos.mpr ⟨(false,x),hClassSelf⟩
  have hOrder :
      Fintype.card Q * t = 2 * Fintype.card V := by
    calc
      Fintype.card Q * t = Fintype.card (Bool × V) :=
        closedTwinQuotient_card_mul_class_of_transitive
          H hTrans (false,x)
      _ = 2 * Fintype.card V := by
        simp [Fintype.card_prod]
  have hCapacity : Fintype.card V ≤ I.card * t := by
    simpa only [H,I,Q,t] using
      (selected_twin_occupied_capacity
        H (EPPAIII.DoubleCover.bottomEmbedding V) t hUniform)
  have hIndependent : 2 * I.card ≤ Fintype.card Q := by
    simpa only [H,I,Q] using
      (taylor_selected_quotient_independent_half
        G heppa hTrans hEven x y hXY hTwin)
  exact occupied_quotient_numerical_equalities
    (Fintype.card V) (Fintype.card Q) t I.card
    ht hOrder hCapacity hIndependent

end EPPAIII.TwoGraphs
