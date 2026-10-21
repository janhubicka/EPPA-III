import EPPAIII.TwoGraphs.TransversalParity
import EPPAIII.TwoGraphs.OneForAll

/-!
# Partial two-graph switching: the fixed-point case

If a partial two-graph automorphism fixes a vertex r in its domain,
switch the graph so that r becomes isolated. Adjacency in this
representative is then exactly the two-graph parity of the triple
(r,x,y), so the partial map preserves every edge and nonedge.

This validates the fixed-point (including identity-map) branch of
the original Section 5.1 partial-switching lemma without any cycle
decomposition. Open paths and fixed points need no prior chosen pair.
-/

namespace EPPAIII.TwoGraphs

/-- Switch with respect to the neighbourhood of the anchor. -/
def anchorSwitch {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) : V → Bool :=
  fun x => decide (G.Adj r x)

/-- In the anchored representative, an edge x--y is precisely
an odd-edge-parity triple (r,x,y). This includes repeated
vertices; no distinctness hypothesis is needed. -/
theorem anchored_transversal_adj_iff_odd
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r x y : V) :
    (taylorTransversalGraph G (anchorSwitch G r)).Adj x y ↔
      OddBaseTriple G r x y := by
  classical
  have hSym :
      decide (G.Adj y r) = decide (G.Adj r y) := by
    by_cases h : G.Adj r y
    · have h' : G.Adj y r := (G.adj_comm r y).mp h
      simp [h,h']
    · have h' : ¬ G.Adj y r :=
        fun hy => h ((G.adj_comm r y).mpr hy)
      simp [h,h']
  have hBool :
      decide ((taylorTransversalGraph G (anchorSwitch G r)).Adj x y) =
        Bool.xor
          (Bool.xor (decide (G.Adj r x)) (decide (G.Adj x y)))
          (decide (G.Adj y r)) := by
    rw [taylor_transversal_decide_adj G (anchorSwitch G r) x y]
    rw [hSym]
    change Bool.xor (decide (G.Adj x y))
        (Bool.xor (decide (G.Adj r x)) (decide (G.Adj r y))) =
      Bool.xor (Bool.xor (decide (G.Adj r x))
        (decide (G.Adj x y))) (decide (G.Adj r y))
    cases ha : decide (G.Adj r x) <;>
      cases hb : decide (G.Adj x y) <;>
      cases hc : decide (G.Adj r y) <;> decide
  constructor
  · intro hAdj
    have hh :
        decide ((taylorTransversalGraph G (anchorSwitch G r)).Adj x y) =
          true := by simpa using hAdj
    change Bool.xor (Bool.xor (decide (G.Adj r x))
      (decide (G.Adj x y))) (decide (G.Adj y r)) = true
    exact hBool.symm.trans hh
  · intro hOdd
    have hh :
        decide ((taylorTransversalGraph G (anchorSwitch G r)).Adj x y) =
          true := by
      exact hBool.trans hOdd
    simpa using hh

/-- A partial automorphism of the two-graph which fixes an
anchor has an explicitly constructed graph representative
on which it is a partial graph automorphism. -/
theorem partial_two_graph_fixed_point_switch
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (p : Equiv.Perm V)
    (hp : IsPartialTwoGraphAutomorphism G D p)
    (r : V) (hr : r ∈ D) (hFix : p r = r) :
    ∃ t : V → Bool,
      EPPAIII.IsPartialGraphAutomorphism
        (taylorTransversalGraph G t) D p := by
  refine ⟨anchorSwitch G r, ?_⟩
  intro x y hx hy
  calc
    (taylorTransversalGraph G (anchorSwitch G r)).Adj x y
        ↔ OddBaseTriple G r x y :=
          anchored_transversal_adj_iff_odd G r x y
    _ ↔ OddBaseTriple G (p r) (p x) (p y) :=
      hp r hr x hx y hy
    _ ↔ OddBaseTriple G r (p x) (p y) := by rw [hFix]
    _ ↔ (taylorTransversalGraph G (anchorSwitch G r)).Adj
        (p x) (p y) :=
      (anchored_transversal_adj_iff_odd G r (p x) (p y)).symm

end EPPAIII.TwoGraphs
