import EPPAIII.BlockSystems.RookThreeTriangleCertificates

/-!
# Checking and reconstructing the actual adjacency of rook doubles

The four 18-vertex rook doubles were defined using SimpleGraph.fromRel.
We certify that the binary relation is already irreflexive and
symmetric, so the construction does not alter its adjacency.

A reusable graph-extensionality theorem identifies any labelled
two-half host with one of these four canonical graphs once the
four layer adjacencies are known. This is the exact bridge needed
to apply the finite triangle-count obstruction to an arbitrary
R3 EPPA witness after canonically labelling the outside half.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- The canonical rook double adjacency agrees with its explicit
four-pattern binary relation, in all Boolean layer cases. -/
theorem rookDoubleGraph_adj_iff :
    ∀ topComplement crossNonrook : Bool,
    ∀ u v : Bool × rookVertex,
      (rookDoubleGraph topComplement crossNonrook).Adj u v ↔
        rookDoubleRelation topComplement crossNonrook u v := by
  decide

/-- The four adjacency restrictions completely determine any graph
on two labelled copies of the nine rook vertices. -/
theorem rookDouble_graph_eq_of_layer_data
    (J : SimpleGraph (Bool × rookVertex))
    (topComplement crossNonrook : Bool)
    (hBB : ∀ x y : rookVertex,
      J.Adj (false,x) (false,y) ↔ rookThreeGraph.Adj x y)
    (hTT : ∀ x y : rookVertex,
      J.Adj (true,x) (true,y) ↔
        (if topComplement then
          x ≠ y ∧ ¬ rookThreeGraph.Adj x y
         else rookThreeGraph.Adj x y))
    (hBT : ∀ x y : rookVertex,
      J.Adj (false,x) (true,y) ↔
        (if crossNonrook then
          x ≠ y ∧ ¬ rookThreeGraph.Adj x y
         else rookThreeGraph.Adj x y))
    (hTB : ∀ x y : rookVertex,
      J.Adj (true,x) (false,y) ↔
        (if crossNonrook then
          x ≠ y ∧ ¬ rookThreeGraph.Adj x y
         else rookThreeGraph.Adj x y)) :
    J = rookDoubleGraph topComplement crossNonrook := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rcases u with ⟨b,x⟩
  rcases v with ⟨c,y⟩
  cases b <;> cases c
  · rw [rookDoubleGraph_adj_iff]
    simpa [rookDoubleRelation] using hBB x y
  · rw [rookDoubleGraph_adj_iff]
    simpa [rookDoubleRelation] using hBT x y
  · rw [rookDoubleGraph_adj_iff]
    simpa [rookDoubleRelation] using hTB x y
  · rw [rookDoubleGraph_adj_iff]
    simpa [rookDoubleRelation] using hTT x y

end EPPAIII.BlockSystems
