import EPPAIII.BlockSystems.RookThreeSmallSubsetOrbits
import EPPAIII.DoubleCover.TriangleTransport

/-!
# Exact finite triangle certificates for the R3 exceptional doubles

Use the nine-vertex rook graph on Fin 3 × Fin 3 as the selected
bottom half. The top half is either the rook graph or its
complement; the cross relation is either rook adjacency or
strict rook nonadjacency. This gives four canonical 18-vertex
graphs, with no fibre-mate edges.

The exact ordered triangle counts through a bottom and a top
vertex are verified by kernel computation:

  top rook,       cross rook:       16 / 16
  top rook,       cross nonrook:    28 / 28
  top complement, cross rook:       20 / 24
  top complement, cross nonrook:    24 / 20.

Thus either complementary-top pattern violates vertex
transitivity. The bridge to the actual graph-theoretic ordered
triangle count is also provided, so the certificate can be used
after the outside-half has been identified up to isomorphism.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Adjacency data for a canonical two-layer rook-graph double. -/
abbrev rookDoubleRelation (topComplement crossNonrook : Bool)
    (u v : Bool × rookVertex) : Prop :=
  if u.1 = v.1 then
    if u.1 = false then rookThreeGraph.Adj u.2 v.2
    else if topComplement then u.2 ≠ v.2 ∧ ¬ rookThreeGraph.Adj u.2 v.2
    else rookThreeGraph.Adj u.2 v.2
  else if crossNonrook then
    u.2 ≠ v.2 ∧ ¬ rookThreeGraph.Adj u.2 v.2
  else rookThreeGraph.Adj u.2 v.2

/-- The actual loopless undirected graph determined by the four
choices; fromRel symmetrises and discards possible loops. -/
def rookDoubleGraph (topComplement crossNonrook : Bool) :
    SimpleGraph (Bool × rookVertex) :=
  SimpleGraph.fromRel (rookDoubleRelation topComplement crossNonrook)

instance (topComplement crossNonrook : Bool) :
    DecidableRel (rookDoubleGraph topComplement crossNonrook).Adj := by
  intro u v
  change Decidable
    (u ≠ v ∧
      (rookDoubleRelation topComplement crossNonrook u v ∨
       rookDoubleRelation topComplement crossNonrook v u))
  infer_instance

/-- Computable number of ordered adjacent neighbour pairs through
one vertex. Each unordered triangle through the root is counted twice. -/
def rookDoubleOrderedTriangles (topComplement crossNonrook : Bool)
    (u : Bool × rookVertex) : ℕ :=
  ((Finset.univ : Finset ((Bool × rookVertex) × (Bool × rookVertex))).filter
    (fun yz =>
      (rookDoubleGraph topComplement crossNonrook).Adj u yz.1 ∧
      (rookDoubleGraph topComplement crossNonrook).Adj u yz.2 ∧
      (rookDoubleGraph topComplement crossNonrook).Adj yz.1 yz.2)).card

/-- The finite definition agrees with the general graph-level
ordered triangle count already used in the Taylor proof. -/
theorem rookDoubleOrderedTriangles_eq_actual
    (topComplement crossNonrook : Bool)
    (u : Bool × rookVertex) :
    rookDoubleOrderedTriangles topComplement crossNonrook u =
      (DoubleCover.orderedTrianglePairsAt
        (rookDoubleGraph topComplement crossNonrook) u).card := by
  classical
  unfold rookDoubleOrderedTriangles
  congr 1
  ext yz
  simp [DoubleCover.orderedTrianglePairsAt]

/-- Both candidate doubles with a complementary top layer have
different bottom and top triangle counts. -/
theorem rookDouble_bad_triangle_counts :
    rookDoubleOrderedTriangles true false (false,(0,0)) = 20 ∧
    rookDoubleOrderedTriangles true false (true,(0,0)) = 24 ∧
    rookDoubleOrderedTriangles true true (false,(0,0)) = 24 ∧
    rookDoubleOrderedTriangles true true (true,(0,0)) = 20 := by
  decide

/-- The two remaining top-rook patterns have matching
bottom and top triangle counts, as required for transitivity. -/
theorem rookDouble_surviving_triangle_counts :
    rookDoubleOrderedTriangles false false (false,(0,0)) = 16 ∧
    rookDoubleOrderedTriangles false false (true,(0,0)) = 16 ∧
    rookDoubleOrderedTriangles false true (false,(0,0)) = 28 ∧
    rookDoubleOrderedTriangles false true (true,(0,0)) = 28 := by
  decide

end EPPAIII.BlockSystems
