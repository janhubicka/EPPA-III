import Mathlib

/-!
# Exact induced-five-cycle certificates in binary polar graph models

Seven **finite base certificates** for the proposed repair of
EPPA III, Section 8. Vertex labels encode bits in least-significant-bit
first order. Each closed statement certifies five distinct permitted
vertices, all five cycle edges, and all five missing chords. Lean checks
the closed arithmetic proofs by reduction.

Scope: these certificates do not prove that the manuscript's larger
polar graphs are the standard models, or that generalized clique covers
have no induced C5. Those are separate obligations.
-/

namespace EPPAIII.BlockSystems.BinaryFiveCycles

def bit (n k : ℕ) : ℕ := n / 2 ^ k % 2

def quadPlus (n : ℕ) : ℕ :=
  (bit n 0 * bit n 3 + bit n 1 * bit n 4 + bit n 2 * bit n 5) % 2

def quadMinus (n : ℕ) : ℕ :=
  (bit n 0 * bit n 2 + bit n 1 * bit n 3 +
   bit n 4 + bit n 5 + bit n 4 * bit n 5) % 2

def polarPlus (a b : ℕ) : ℕ :=
  (bit a 0 * bit b 3 + bit a 3 * bit b 0 +
   bit a 1 * bit b 4 + bit a 4 * bit b 1 +
   bit a 2 * bit b 5 + bit a 5 * bit b 2) % 2

def polarMinus (a b : ℕ) : ℕ :=
  (bit a 0 * bit b 2 + bit a 2 * bit b 0 +
   bit a 1 * bit b 3 + bit a 3 * bit b 1 +
   bit a 4 * bit b 5 + bit a 5 * bit b 4) % 2

def symplecticFour (a b : ℕ) : ℕ :=
  (bit a 0 * bit b 2 + bit a 2 * bit b 0 +
   bit a 1 * bit b 3 + bit a 3 * bit b 1) % 2

def isSpFourVertex (x : ℕ) : Prop := 0 < x ∧ x < 16

def isOrthogonalVertex (plus singular : Bool) (x : ℕ) : Prop :=
  0 < x ∧ x < 64 ∧
   ((if plus then quadPlus x else quadMinus x) = 0 ↔ singular = true)

def isVectorVertex (x : ℕ) : Prop := x < 64

def orthogonalAdj (plus : Bool) (a b : ℕ) : Prop :=
  a ≠ b ∧ (if plus then polarPlus a b else polarMinus a b) = 0

def vectorAdj (plus : Bool) (a b : ℕ) : Prop :=
  a ≠ b ∧
    (if plus then (quadPlus a + quadPlus b + polarPlus a b) % 2
     else (quadMinus a + quadMinus b + polarMinus a b) % 2) = 0

def symplecticAdj (a b : ℕ) : Prop :=
  a ≠ b ∧ symplecticFour a b = 0

/-- Precisely an induced five-cycle with five distinct admissible vertices. -/
def IsInducedFiveCycleOn
    (vertex : ℕ → Prop) (adj : ℕ → ℕ → Prop)
    (a b c d e : ℕ) : Prop :=
  (vertex a ∧ vertex b ∧ vertex c ∧ vertex d ∧ vertex e) ∧
  (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
   b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ c ≠ d ∧ c ≠ e ∧ d ≠ e) ∧
  (adj a b ∧ adj b c ∧ adj c d ∧ adj d e ∧ adj e a) ∧
  (¬ adj a c ∧ ¬ adj a d ∧ ¬ adj b d ∧ ¬ adj b e ∧ ¬ adj c e)

set_option maxRecDepth 4096
set_option maxHeartbeats 0

theorem spFour_five_cycle :
    IsInducedFiveCycleOn isSpFourVertex symplecticAdj 1 2 4 12 11 := by
  decide

theorem oSixPlus_five_cycle :
    IsInducedFiveCycleOn
      (isOrthogonalVertex true true) (orthogonalAdj true)
      1 2 8 24 55 := by
  decide

theorem oSixMinus_five_cycle :
    IsInducedFiveCycleOn
      (isOrthogonalVertex false true) (orthogonalAdj false)
      1 2 4 12 27 := by
  decide

theorem noSixPlus_five_cycle :
    IsInducedFiveCycleOn
      (isOrthogonalVertex true false) (orthogonalAdj true)
      9 11 19 37 52 := by
  decide

theorem noSixMinus_five_cycle :
    IsInducedFiveCycleOn
      (isOrthogonalVertex false false) (orthogonalAdj false)
      5 7 11 17 24 := by
  decide

theorem voSixPlus_five_cycle :
    IsInducedFiveCycleOn isVectorVertex (vectorAdj true)
      0 1 9 18 47 := by
  decide

theorem voSixMinus_five_cycle :
    IsInducedFiveCycleOn isVectorVertex (vectorAdj false)
      0 1 5 10 23 := by
  decide

end EPPAIII.BlockSystems.BinaryFiveCycles
