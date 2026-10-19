import EPPAIII.TwoGraphs.TaylorFibresDistance
import EPPAIII.CliqueCovers.ClosedTwinClasses

/-!
# Taylor bad pairs yield adjacent true twins

In the source's fibre-rigidity proof, a pair which is contained
only in odd two-graph triples admits adjacent lifts whose closed
neighbourhoods coincide. This is the first step of the true-twin
quotient reduction. No EPPA, group transitivity, or classification
input is used in this local adjacency calculation.
-/

namespace EPPAIII.TwoGraphs

/-- Boolean compatibility of the neighbours of two adjacent
lifts over a third base point in an odd triple. -/
theorem odd_triple_adjacent_lifts_agree
    {V : Type*} (G : SimpleGraph V)
    (x y z : V) (b c d : Bool)
    (hXY : G.Adj x y ↔ b = c)
    (hOdd : ¬ EvenTriple G x y z) :
    (G.Adj x z ↔ b = d) ↔
      (G.Adj y z ↔ c = d) := by
  unfold EvenTriple at hOdd
  by_cases eXY : G.Adj x y <;>
    by_cases eXZ : G.Adj x z <;>
    by_cases eYZ : G.Adj y z <;>
    cases b <;> cases c <;> cases d <;>
    simp_all

/-- If x,y belong only to odd triples, then any adjacent
lifts have equal adjacency to every point over a third
base vertex. -/
theorem taylor_bad_pair_same_third_fibre_neighbours
    {V : Type*}
    (G : SimpleGraph V) (x y : V) (b c : Bool)
    (hAdj : (taylorPairGraph G).Adj (b,x) (c,y))
    (hBad : ∀ z : V, x ≠ z → y ≠ z →
      ¬ EvenTriple G x y z)
    (z : V) (d : Bool) (hxz : x ≠ z) (hyz : y ≠ z) :
    (taylorPairGraph G).Adj (b,x) (d,z) ↔
      (taylorPairGraph G).Adj (c,y) (d,z) := by
  have hXY : G.Adj x y ↔ b = c := hAdj.2
  have h := odd_triple_adjacent_lifts_agree
    G x y z b c d hXY (hBad z hxz hyz)
  change (x ≠ z ∧ (G.Adj x z ↔ b = d)) ↔
    (y ≠ z ∧ (G.Adj y z ↔ c = d))
  constructor
  · rintro ⟨_,hLeft⟩
    exact ⟨hyz,h.mp hLeft⟩
  · rintro ⟨_,hRight⟩
    exact ⟨hxz,h.mpr hRight⟩

/-- Under the same hypothesis, the two adjacent lifts are
actual true twins of the entire Taylor graph, including their
relations inside the two distinguished fibres. -/
theorem taylor_bad_pair_adjacent_true_twins
    {V : Type*} (G : SimpleGraph V)
    (x y : V) (b c : Bool)
    (hAdj : (taylorPairGraph G).Adj (b,x) (c,y))
    (hBad : ∀ z : V, x ≠ z → y ≠ z →
      ¬ EvenTriple G x y z) :
    EPPAIII.CliqueCovers.SameClosedNeighbourhood
      (taylorPairGraph G) (b,x) (c,y) := by
  apply EPPAIII.CliqueCovers.closedNeighbourhood_eq_of_true_twins
    (taylorPairGraph G) (b,x) (c,y) hAdj
  intro w hwu hwv
  rcases w with ⟨d,z⟩
  by_cases hzx : z = x
  · subst z
    have hBase := hAdj.2
    have hSym : G.Adj y x ↔ G.Adj x y := G.adj_comm y x
    cases b <;> cases c <;> cases d <;>
      by_cases eXY : G.Adj x y <;>
      simp_all [taylorPairGraph, taylorPairAdj]
  · by_cases hzy : z = y
    · subst z
      have hBase := hAdj.2
      have hSym : G.Adj y x ↔ G.Adj x y := G.adj_comm y x
      cases b <;> cases c <;> cases d <;>
        by_cases eXY : G.Adj x y <;>
        simp_all [taylorPairGraph, taylorPairAdj]
    · have hxz : x ≠ z := fun h => hzx h.symm
      have hyz : y ≠ z := fun h => hzy h.symm
      exact taylor_bad_pair_same_third_fibre_neighbours
        G x y b c hAdj hBad z d hxz hyz

end EPPAIII.TwoGraphs
