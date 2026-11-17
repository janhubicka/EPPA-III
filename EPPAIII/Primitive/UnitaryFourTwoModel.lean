import EPPAIII.Primitive.UnitaryFourTwoArithmetic
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fin.VecNotation

/-! # The Hermitian point graph of order 45 -/

namespace EPPAIII.Primitive.UnitaryFourTwo

/-- The graph vertices are indexed by the increasing list of normalized
isotropic representatives in the Hermitian coordinate model. -/
def coordinatesOfIndex (i : Fin 45) : Nat :=
  vertices[i.val]'(by rw [order_eq]; exact i.isLt)

/-- Adjacency rows in these coordinates. -/
private def adjacencyRows : Fin 45 → ℕ :=
  ![5052114966528, 10069861804032, 20105355479040, 498337870848, 18773590479360, 3866414515200, 9631668158976, 30811027670016,
    6744745320960, 2093392, 20068536979624, 30787265130503, 4673093307929, 8882328308490, 17730183400012, 2303445190241,
    741419782706, 1413182923556, 18144114648961, 5519074968258, 10996269781652, 8573157712, 10034269536424, 3848409972743,
    691773128729, 1376011162890, 2287215845452, 5499779160161, 10999430163506, 18160231205156, 8899750035841, 17764188488898,
    4724751990932, 35115652612432, 5021421346984, 488552759303, 18752968106009, 6642187976970, 9393127167052, 9097303097441,
    17669676466226, 4544420414756, 2366661728641, 834571086018, 1179505675412]

private def adjacentByIndex (i j : Fin 45) : Bool :=
  (adjacencyRows i).testBit j.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- The adjacency table agrees with the Hermitian orthogonality test. -/
theorem index_adjacent_agrees : ∀ i j,
    adjacentByIndex i j = adjacent (coordinatesOfIndex i) (coordinatesOfIndex j) := by
  decide

/-- Orthogonality on distinct isotropic points gives the collinearity graph. -/
def graph : SimpleGraph (Fin 45) where
  Adj i j := adjacentByIndex i j = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun _ _ => by
  unfold graph
  infer_instance

theorem graph_adj_coordinates (i j : Fin 45) :
    graph.Adj i j ↔ adjacent (coordinatesOfIndex i) (coordinatesOfIndex j) = true := by
  change adjacentByIndex i j = true ↔ _
  rw [index_adjacent_agrees]

/-- The point `(0,0,1,1)`. -/
def root : Fin 45 := 11

/-- The twelve neighbours of the chosen point, in increasing index order. -/
def localPoint : Fin 12 → Fin 45 := ![0, 1, 2, 12, 13, 14, 27, 28,
    29, 42, 43, 44]

theorem localPoint_injective : Function.Injective localPoint := by decide

theorem localPoint_range : ∀ p, graph.Adj root p ↔ ∃ i, localPoint i = p := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem graph_isSRG : graph.IsSRGWith 45 12 3 3 := by
  constructor
  · decide
  · change ∀ x, graph.degree x = 12
    decide
  · decide
  · change ∀ x y, x ≠ y → ¬graph.Adj x y →
      Fintype.card (graph.commonNeighbors x y) = 3
    decide

end EPPAIII.Primitive.UnitaryFourTwo
