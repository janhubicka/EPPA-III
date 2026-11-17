import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Fin.Bitwise
import Init.Data.List.FinRange
import EPPAIII.BlockSystems.BinaryFiveCycleCertificates

/-!
# The certificate generators on binary vector coordinates

The forward matrices are the six basis-image lists from
`checks/section8_binary_negative.py`. Lean checks the supplied inverse
matrices and preservation of the quadratic form on all 64 vectors.
The XOR-linearity proof works for every list of basis images.
-/

namespace EPPAIII.Primitive

open BlockSystems.BinaryFiveCycles

private def generatorColumns (plus : Bool) (gen : Fin 3) : List (Fin 64) :=
  let data : List (List (Fin 64)) := if plus then
    [[8, 62, 42, 47, 2, 14], [62, 14, 54, 45, 28, 33], [10, 2, 4, 3, 27, 32]]
  else
    [[15, 58, 62, 37, 28, 10], [30, 43, 1, 59, 25, 19], [61, 62, 4, 8, 44, 28]]
  data[gen.val]?.getD []

private def inverseColumns (plus : Bool) (gen : Fin 3) : List (Fin 64) :=
  let data : List (List (Fin 64)) := if plus then
    [[61, 16, 49, 1, 55, 21], [27, 42, 45, 5, 56, 59], [10, 2, 4, 3, 27, 32]]
  else
    [[39, 61, 6, 29, 11, 41], [4, 46, 59, 30, 10, 54], [61, 62, 4, 8, 44, 28]]
  data[gen.val]?.getD []

private def columnSum (columns : List (Fin 64)) (x : Nat) : List Nat → Nat
  | [] => 0
  | i :: is => (if x.testBit i then (columns[i]?.getD 0).val else 0) ^^^
      columnSum columns x is

private theorem columnSum_lt (columns : List (Fin 64)) (x : Nat) (indices : List Nat) :
    columnSum columns x indices < 64 := by
  induction indices with
  | nil => simp [columnSum]
  | cons i is ih =>
      unfold columnSum
      exact Nat.xor_lt_two_pow (n := 6)
        (by split <;> first | exact Fin.isLt _ | decide) ih

private theorem select_xor (a b : Bool) (v : Nat) :
    (if Bool.xor a b then v else 0) =
      (if a then v else 0) ^^^ (if b then v else 0) := by
  cases a <;> cases b <;> simp

private theorem columnSum_xor (columns : List (Fin 64)) (x y : Nat) (indices : List Nat) :
    columnSum columns (x ^^^ y) indices =
      columnSum columns x indices ^^^ columnSum columns y indices := by
  induction indices with
  | nil => simp [columnSum]
  | cons i is ih =>
      simp only [columnSum, Nat.testBit_xor, select_xor, ih]
      ac_rfl

private def binaryLinearMap (columns : List (Fin 64)) (x : Fin 64) : Fin 64 :=
  ⟨columnSum columns x.val (List.range 6), columnSum_lt _ _ _⟩

private theorem binaryLinearMap_xor (columns : List (Fin 64)) (x y : Fin 64) :
    binaryLinearMap columns (x ^^^ y) = binaryLinearMap columns x ^^^ binaryLinearMap columns y := by
  apply Fin.ext
  simp only [Fin.xor_val_of_two_pow (w := 6), binaryLinearMap]
  exact columnSum_xor _ _ _ _

/-- The tested linear map at a certificate generator index. -/
def binaryOrthogonalGeneratorValue (plus : Bool) (gen : Fin 3) (x : Fin 64) : Fin 64 :=
  binaryLinearMap (generatorColumns plus gen) x

/-- The inverse coordinate map, verified below on every vector. -/
def binaryOrthogonalGeneratorInverseValue (plus : Bool) (gen : Fin 3) (x : Fin 64) : Fin 64 :=
  binaryLinearMap (inverseColumns plus gen) x

private def checksInverse (p : Bool) (g : Fin 3) (x : Fin 64) : Bool :=
  binaryOrthogonalGeneratorInverseValue p g (binaryOrthogonalGeneratorValue p g x) == x &&
  binaryOrthogonalGeneratorValue p g (binaryOrthogonalGeneratorInverseValue p g x) == x

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem inverseCheck : ([false, true] : List Bool).all (fun p =>
    (List.finRange 3).all fun g => (List.finRange 64).all (checksInverse p g)) = true := by
  decide

theorem binaryOrthogonalGenerator_inverse_laws (p : Bool) (g : Fin 3) (x : Fin 64) :
    binaryOrthogonalGeneratorInverseValue p g (binaryOrthogonalGeneratorValue p g x) = x ∧
      binaryOrthogonalGeneratorValue p g (binaryOrthogonalGeneratorInverseValue p g x) = x := by
  have hp : p ∈ [false, true] := by cases p <;> simp
  have h := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp inverseCheck p hp) g (List.mem_finRange g)) x (List.mem_finRange x)
  simpa only [checksInverse, Bool.and_eq_true_iff, beq_iff_eq] using h

theorem binaryOrthogonalGeneratorValue_xor (plus : Bool) (gen : Fin 3) (x y : Fin 64) :
    binaryOrthogonalGeneratorValue plus gen (x ^^^ y) =
      binaryOrthogonalGeneratorValue plus gen x ^^^ binaryOrthogonalGeneratorValue plus gen y :=
  binaryLinearMap_xor _ x y

theorem binaryOrthogonalGeneratorValue_zero (plus : Bool) (gen : Fin 3) :
    binaryOrthogonalGeneratorValue plus gen 0 = 0 := by
  unfold binaryOrthogonalGeneratorValue binaryLinearMap
  apply Fin.ext
  change columnSum (generatorColumns plus gen) 0 (List.range 6) = 0
  induction (List.range 6) with
  | nil => rfl
  | cons i is ih =>
      simpa only [columnSum, Nat.zero_testBit, Bool.false_eq_true,
        ite_false, Nat.zero_xor] using ih

private def preservesQuadratic : Bool → Fin 3 → Fin 64 → Bool
  | true, gen, x => quadPlus (binaryOrthogonalGeneratorValue true gen x).val == quadPlus x.val
  | false, gen, x => quadMinus (binaryOrthogonalGeneratorValue false gen x).val == quadMinus x.val

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem quadraticCheck : ([false, true] : List Bool).all (fun p =>
    (List.finRange 3).all fun g => (List.finRange 64).all (preservesQuadratic p g)) = true := by
  decide

theorem binaryOrthogonalGeneratorValue_quadratic (plus : Bool) (gen : Fin 3) (x : Fin 64) :
    (if plus then quadPlus (binaryOrthogonalGeneratorValue plus gen x).val else
      quadMinus (binaryOrthogonalGeneratorValue plus gen x).val) =
    (if plus then quadPlus x.val else quadMinus x.val) := by
  have hp : plus ∈ [false, true] := by cases plus <;> simp
  have h := List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp quadraticCheck plus hp) gen (List.mem_finRange gen)) x (List.mem_finRange x)
  cases plus <;> simpa only [preservesQuadratic, Bool.false_eq_true, ite_false, ite_true,
    beq_iff_eq] using h

end EPPAIII.Primitive
