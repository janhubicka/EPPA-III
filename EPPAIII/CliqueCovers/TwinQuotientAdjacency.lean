import EPPAIII.CliqueCovers.ClosedTwinClasses

/-!
# Adjacency is well defined between distinct closed-neighbourhood classes

The zero-partial-profile proof passes to the quotient of the host
by equality of closed neighbourhoods. An equivalence class is a clique,
so quotient adjacency must omit loops. To show that the quotient graph
is well defined, one needs adjacency between *distinct* classes to
be independent of the chosen representatives.

This file proves that statement directly, using only the definition
of the closed-neighbourhood equivalence relation. It does not assume
vertex-transitivity, EPPA or any special form of the original graph.
-/

namespace EPPAIII.CliqueCovers

/-- When two vertices have the same closed neighbourhood, any
third vertex distinct from both is adjacent to either both or neither. -/
theorem adj_iff_of_same_closed_neighbourhood_left {W : Type*}
    (H : SimpleGraph W) (u u' v : W)
    (hu : SameClosedNeighbourhood H u u')
    (huv : u ≠ v) (hu'v : u' ≠ v) :
    H.Adj u v ↔ H.Adj u' v := by
  change closedNeighbourhood H u = closedNeighbourhood H u' at hu
  constructor
  · intro h
    have hv : v ∈ closedNeighbourhood H u := Or.inr h
    rw [hu] at hv
    change v = u' ∨ H.Adj u' v at hv
    rcases hv with hEq | hAdj
    · exact False.elim (hu'v hEq.symm)
    · exact hAdj
  · intro h
    have hv : v ∈ closedNeighbourhood H u' := Or.inr h
    rw [← hu] at hv
    change v = u ∨ H.Adj u v at hv
    rcases hv with hEq | hAdj
    · exact False.elim (huv hEq.symm)
    · exact hAdj

/-- Representatives of different twin classes are distinct. -/
theorem distinct_representatives_of_distinct_twin_classes {W : Type*}
    (H : SimpleGraph W) (u u' v v' : W)
    (hu : SameClosedNeighbourhood H u u')
    (hv : SameClosedNeighbourhood H v v')
    (hDifferent : ¬ SameClosedNeighbourhood H u v) :
    u' ≠ v' := by
  intro hEq
  apply hDifferent
  change closedNeighbourhood H u = closedNeighbourhood H u' at hu
  change closedNeighbourhood H v = closedNeighbourhood H v' at hv
  show closedNeighbourhood H u = closedNeighbourhood H v
  calc
    closedNeighbourhood H u = closedNeighbourhood H u' := hu
    _ = closedNeighbourhood H v' := by rw [hEq]
    _ = closedNeighbourhood H v := hv.symm

/-- Adjacency between two distinct closed-neighbourhood classes is
independent of the chosen representatives. This is the exact
well-definedness lemma for the eventual quotient graph. -/
theorem adj_iff_of_distinct_twin_classes {W : Type*}
    (H : SimpleGraph W) (u u' v v' : W)
    (hu : SameClosedNeighbourhood H u u')
    (hv : SameClosedNeighbourhood H v v')
    (hDifferent : ¬ SameClosedNeighbourhood H u v) :
    H.Adj u v ↔ H.Adj u' v' := by
  have hne_uv : u ≠ v :=
    distinct_representatives_of_distinct_twin_classes
      H u u v v rfl rfl hDifferent
  have hne_u'v : u' ≠ v :=
    distinct_representatives_of_distinct_twin_classes
      H u u' v v hu rfl hDifferent
  have hne_u'v' : u' ≠ v' :=
    distinct_representatives_of_distinct_twin_classes
      H u u' v v' hu hv hDifferent
  calc
    H.Adj u v ↔ H.Adj u' v :=
      adj_iff_of_same_closed_neighbourhood_left
        H u u' v hu hne_uv hne_u'v
    _ ↔ H.Adj v u' := H.adj_comm u' v
    _ ↔ H.Adj v' u' :=
      adj_iff_of_same_closed_neighbourhood_left
        H v v' u' hv hne_u'v.symm hne_u'v'.symm
    _ ↔ H.Adj u' v' := H.adj_comm v' u'

end EPPAIII.CliqueCovers
