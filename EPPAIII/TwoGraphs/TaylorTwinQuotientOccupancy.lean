import EPPAIII.TwoGraphs.TrueTwinTransversalHomogeneity
import EPPAIII.TwoGraphs.EPPAEdgeTwinPropagation
import EPPAIII.TwoGraphs.TaylorBadPairTwins
import EPPAIII.CliqueCovers.TwinQuotientAction
import EPPAIII.DoubleCover.DeckSwap

/-!
# Selected true-twin quotient occupancy in Taylor fibre rigidity

The manuscript's first true-twin-quotient case requires:
(1) all selected edges lie in one twin class, so selected
    quotient classes form an independent set;
(2) the Taylor deck involution exchanges distinct twin
    classes and acts without fixed quotient points.

These lemmas certify exactly those structural inputs.
The cardinality and positive-degree regularity arguments
remain distinct follow-up obligations.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- If all selected edges join true twins in the actual host,
the twin quotient classes meeting the selected graph form an
independent set. No transitivity or Taylor hypothesis is needed. -/
theorem selected_twin_quotient_range_independent
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W)
    (hInduced : IsInducedGraphEmbedding G H e)
    (hEdgeTwin : ∀ x y : V, G.Adj x y →
      SameClosedNeighbourhood H (e x) (e y)) :
    (closedTwinQuotientGraph H).IsIndepSet
      (Set.range (fun x : V =>
        Quotient.mk (closedTwinSetoid H) (e x))) := by
  intro a ha b hb hab hq
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  subst a
  subst b
  have hQuot :=
    (closedTwinQuotient_adj_mk H (e x) (e y)).mp hq
  have hBase : G.Adj x y := (hInduced x y).mpr hQuot.2
  exact hQuot.1 (hEdgeTwin x y hBase)

/-- Actual EPPA of the selected graph suffices to propagate one
twin edge and make its occupied true-twin classes independent. -/
theorem eppa_selected_twin_classes_independent
    {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (x y : V) (hEdge : G.Adj x y)
    (hTwin : SameClosedNeighbourhood H (e x) (e y)) :
    (closedTwinQuotientGraph H).IsIndepSet
      (Set.range (fun v : V =>
        Quotient.mk (closedTwinSetoid H) (e v))) := by
  apply selected_twin_quotient_range_independent G H e heppa.1
  intro u v huv
  exact eppa_true_twins_propagate_to_all_edges
    G H e heppa x y hEdge hTwin u v huv

/-- Simultaneously flipping both side bits is an automorphism
of the canonical Taylor double. -/
theorem taylor_deck_graph_automorphism {V : Type*}
    (G : SimpleGraph V) :
    IsGraphAutomorphism (taylorPairGraph G)
      (EPPAIII.DoubleCover.deckSwap V) := by
  rintro ⟨b,x⟩ ⟨c,y⟩
  change (x ≠ y ∧ (G.Adj x y ↔ b = c)) ↔
    (x ≠ y ∧ (G.Adj x y ↔ !b = !c))
  cases b <;> cases c <;> simp

/-- A vertex and its mate cannot be true twins because mates are
nonadjacent and different true twins must be adjacent. -/
theorem taylor_mates_not_true_twins
    {V : Type*} (G : SimpleGraph V)
    (b : Bool) (x : V) :
    ¬ SameClosedNeighbourhood
      (taylorPairGraph G) (b,x) (!b,x) := by
  intro hTwin
  have hNe : (b,x) ≠ (!b,x) := by
    intro h
    have hh := congrArg Prod.fst h
    cases b <;> simp at hh
  have hAdj := adjacent_of_same_closed_neighbourhood
    (taylorPairGraph G) (b,x) (!b,x) hNe hTwin
  exact (taylor_mates_not_adj G b x) hAdj

/-- In particular, the deck involution acts without fixed points
on the canonical quotient by true-twin equivalence. -/
theorem taylor_deck_twin_quotient_fixed_point_free
    {V : Type*} (G : SimpleGraph V)
    (z : ClosedTwinQuotient (taylorPairGraph G)) :
    liftTwinAutomorphism (taylorPairGraph G)
      (EPPAIII.DoubleCover.deckSwap V)
      (taylor_deck_graph_automorphism G) z ≠ z := by
  induction z using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨b,x⟩
    intro h
    have hSame : SameClosedNeighbourhood
        (taylorPairGraph G) (!b,x) (b,x) := by
      apply Quotient.exact
      simpa [liftTwinAutomorphism_mk,EPPAIII.DoubleCover.deckSwap] using h
    exact (taylor_mates_not_true_twins G b x) hSame.symm

end EPPAIII.TwoGraphs
