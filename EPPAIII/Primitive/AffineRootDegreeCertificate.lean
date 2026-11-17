import EPPAIII.Primitive.AffineRootMaskData
import EPPAIII.Primitive.BinaryOrthogonalModels
import EPPAIII.Primitive.ClebschSchlafliModels
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Degree test on the enumerated rooted affine candidates

The first check is that the witnessed masks cover the required products of
the local and nonlocal lists. The second check verifies the displayed bad
selected vertex of each candidate.
-/

namespace EPPAIII.Primitive

private def maskProducts (localMasks nonlocalMasks : List Nat) : List Nat :=
  localMasks.flatMap fun a => nonlocalMasks.map fun b => a ||| b ||| 1

/-- All unions of a retained local mask, a nonlocal mask of the
complementary size, and the selected root. -/
def affineRootMaskProducts (plus : Bool) : List Nat :=
  maskProducts (affineLocalMasks15 plus) (affineNonlocalMasks16 plus) ++
    maskProducts (affineLocalMasks16 plus) (affineNonlocalMasks15 plus)

/-- The selected degree of an ambient vertex in a given affine mask. -/
def affineMaskDegree (plus : Bool) (mask : Nat) (v : Fin 64) : Nat :=
  (Finset.univ.filter fun w : Fin 64 =>
    mask.testBit w.val = true ∧ (vectorOrthogonalSixGraph plus).Adj v w).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem affineRootCoverage :
    ∀ plus : Bool, affineRootMaskProducts plus =
      (affineRootCandidates plus).map Prod.fst := by
  decide

private def candidateHasBadDegree (plus : Bool) (candidate : Nat × Fin 64) : Prop :=
  let degree := affineMaskDegree plus candidate.1 candidate.2
  candidate.1.testBit candidate.2.val = true ∧ (degree < 15 ∨ 16 < degree)

private instance (plus : Bool) : DecidablePred (candidateHasBadDegree plus) :=
  fun candidate => by
    unfold candidateHasBadDegree
    infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem affineRootWitnesses :
    ∀ plus : Bool, (affineRootCandidates plus).all
      (fun candidate => decide (candidateHasBadDegree plus candidate)) = true := by
  decide

/-- Every required rooted mask has a selected vertex whose degree violates
the interval 15 through 16. -/
theorem affineRootMask_badDegree (plus : Bool) (mask : Nat)
    (hMask : mask ∈ affineRootMaskProducts plus) :
    ∃ v : Fin 64, v ∈ maskVertices 64 mask ∧
      (affineMaskDegree plus mask v < 15 ∨ 16 < affineMaskDegree plus mask v) := by
  rw [affineRootCoverage plus] at hMask
  obtain ⟨⟨candidate, v⟩, hCandidate, hEq⟩ := List.mem_map.mp hMask
  change candidate = mask at hEq
  subst candidate
  have hChecked := List.all_eq_true.mp (affineRootWitnesses plus) (mask, v) hCandidate
  have hWitness : candidateHasBadDegree plus (mask, v) := of_decide_eq_true hChecked
  exact ⟨v, hWitness⟩

/-- The computed degree is the cardinality of the neighbor set in the
induced graph on the mask. -/
theorem affineMaskDegree_eq_card (plus : Bool) (mask : Nat) (v : maskVertices 64 mask) :
    affineMaskDegree plus mask v.val =
      Nat.card (((vectorOrthogonalSixGraph plus).induce (maskVertices 64 mask)).neighborSet v) := by
  let neighbors := Finset.univ.filter fun w : Fin 64 =>
    mask.testBit w.val = true ∧ (vectorOrthogonalSixGraph plus).Adj v.val w
  let f : (neighbors : Set (Fin 64)) ≃
      ((vectorOrthogonalSixGraph plus).induce (maskVertices 64 mask)).neighborSet v :=
    { toFun := fun w => by
        have hw := (Finset.mem_filter.mp w.property).2
        exact ⟨⟨w.val, hw.1⟩, hw.2⟩
      invFun := fun w => ⟨w.val.val,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.val.property, w.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Set.ncard_coe_finset neighbors).symm.trans (Nat.card_congr f)

end EPPAIII.Primitive
