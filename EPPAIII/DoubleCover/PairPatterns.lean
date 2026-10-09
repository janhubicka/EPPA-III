import Mathlib

/-!
# Two-point fibre patterns for Section 3 of EPPA--III

An invariant pair system, together with two-point EPPA, reduces
inter-fibre adjacency matrices to four binary parameters. The
non-homogeneity argument forces equal edge counts over an edge
and a nonedge of the embedded base graph. This file formally
checks that exactly three binary configurations survive.

It is deliberately not a replacement for the missing Lean proof of
the graph-theoretic orbit-to-matrix reduction.
-/

namespace EPPAIII.DoubleCover

structure PairPattern where
  crossEdge : Bool
  crossNonedge : Bool
  topEdge : Bool
  topNonedge : Bool
  deriving DecidableEq, Repr

/-- Number of edges between fibres above a base edge. -/
def PairPattern.edgeCount (p : PairPattern) : Nat :=
  1 + (if p.crossEdge then 2 else 0) +
    (if p.topEdge then 1 else 0)

/-- Number of edges between fibres above a base nonedge. -/
def PairPattern.nonedgeCount (p : PairPattern) : Nat :=
  (if p.crossNonedge then 2 else 0) +
    (if p.topNonedge then 1 else 0)

def oneEdge : PairPattern :=
  ⟨false, false, false, true⟩

def taylor : PairPattern :=
  ⟨false, true, true, false⟩

def threeEdges : PairPattern :=
  ⟨true, true, false, true⟩

/-- There are exactly three equal-count adjacency patterns.
This is the finite arithmetic step in the two-point EPPA proof. -/
theorem balanced_cases (p : PairPattern)
    (h : p.edgeCount = p.nonedgeCount) :
    p = oneEdge ∨ p = taylor ∨ p = threeEdges := by
  rcases p with ⟨ce, cn, te, tn⟩
  cases ce <;> cases cn <;> cases te <;> cases tn <;>
    simp_all [PairPattern.edgeCount, PairPattern.nonedgeCount,
      oneEdge, taylor, threeEdges]

/-- The Taylor pattern has two inter-fibre edges of each type. -/
theorem taylor_balanced :
    taylor.edgeCount = taylor.nonedgeCount := by
  decide

/-- The other two patterns have one and three inter-fibre edges. -/
theorem exceptional_edge_counts :
    oneEdge.edgeCount = 1 ∧ oneEdge.nonedgeCount = 1 ∧
    threeEdges.edgeCount = 3 ∧ threeEdges.nonedgeCount = 3 := by
  decide

end EPPAIII.DoubleCover
