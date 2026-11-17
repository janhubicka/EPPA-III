/-!
# Finite Hermitian arithmetic for the order-45 unitary graph

The normalized points and orthogonality test are the coordinates used in
the proposed repair of the missing `U₄(2)` case. The two closed statements
check the local vertex list and the six disjoint-edge counts. The passage
from arbitrary selected local sets to these counts is the separate
geometric argument in the review patch.
-/
namespace EPPAIII.Primitive.UnitaryFourTwo

/-- Multiplication with 2 denoting ω and 3 denoting ω² = ω + 1. -/
def mul (a b : Nat) : Nat :=
  match a, b with
  | 0, _ | _, 0 => 0
  | 1, b => b
  | a, 1 => a
  | 2, 2 => 3
  | 3, 3 => 2
  | _, _ => 1

def coordinates (n : Nat) : List Nat :=
  [n % 4, n / 4 % 4, n / 16 % 4, n / 64 % 4]

/-- The normalized nonzero isotropic points of the standard Hermitian form. -/
def vertices : List Nat :=
  (List.range 256).filter fun n =>
    let nonzero := (coordinates n).filter (· != 0)
    nonzero.head? == some 1 && nonzero.length % 2 == 0

def adjacent (a b : Nat) : Bool :=
  a != b &&
    ((coordinates a).zip (coordinates b)).foldl
      (fun sum (x, y) => Nat.xor sum (mul x (mul y y))) 0 == 0

/-- Encode the local point `(1,a,b,b)`. -/
def point (a b : Nat) : Nat := 1 + 4 * a + 80 * b

/-- Common neighbours of the four cross pairs, with `(0,0,1,1)` removed. -/
def crossPairNeighbours (b c : Nat) : List Nat :=
  vertices.filter fun w =>
    w != 80 && ([point 1 0, point 1 1]).any fun x =>
      ([point 2 b, point 2 c]).any fun y =>
        adjacent x w && adjacent y w

def edgeCount (points : List Nat) : Nat :=
  (points.map fun a =>
    (points.filter fun b => decide (a < b) && adjacent a b).length).sum

def crossCounts (b c : Nat) : Nat × Nat :=
  let points := crossPairNeighbours b c
  (points.length, edgeCount points)

theorem order_eq : vertices.length = 45 := by decide

set_option maxRecDepth 4096 in
theorem local_vertices_eq :
    vertices.filter (adjacent 80) =
      (List.range 4).flatMap (fun b => [point 1 b, point 2 b, point 3 b]) := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem disjoint_edge_counts :
    crossCounts 0 1 = (8, 8) ∧ crossCounts 0 2 = (8, 8) ∧
    crossCounts 0 3 = (8, 12) ∧ crossCounts 1 2 = (8, 12) ∧
    crossCounts 1 3 = (8, 8) ∧ crossCounts 2 3 = (8, 8) := by
  decide

end EPPAIII.Primitive.UnitaryFourTwo
