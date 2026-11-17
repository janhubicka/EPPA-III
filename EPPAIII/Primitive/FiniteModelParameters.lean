import EPPAIII.Primitive.BinaryOrthogonalModels
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Parameters of the explicit finite negative models

The graph parameters are checked by reduction over the finite point sets.
They specify the orientation used by the EPPA exclusion assumptions.
-/

namespace EPPAIII.Primitive

set_option maxRecDepth 50000
set_option maxHeartbeats 0

theorem oSixPlus_isSRG : (orthogonalSixGraph true true).IsSRGWith 35 18 9 9 := by
  constructor
  · decide
  · change ∀ v, (orthogonalSixGraph true true).degree v = 18
    decide
  · decide
  · change ∀ v w, v ≠ w → ¬ (orthogonalSixGraph true true).Adj v w →
      Fintype.card ((orthogonalSixGraph true true).commonNeighbors v w) = 9
    decide

theorem noSixMinus_isSRG : (orthogonalSixGraph false false).IsSRGWith 36 15 6 6 := by
  constructor
  · decide
  · change ∀ v, (orthogonalSixGraph false false).degree v = 15
    decide
  · decide
  · change ∀ v w, v ≠ w → ¬ (orthogonalSixGraph false false).Adj v w →
      Fintype.card ((orthogonalSixGraph false false).commonNeighbors v w) = 6
    decide

theorem voSixPlus_isSRG : (vectorOrthogonalSixGraph true).IsSRGWith 64 35 18 20 := by
  constructor
  · decide
  · change ∀ v, (vectorOrthogonalSixGraph true).degree v = 35
    decide
  · decide
  · change ∀ v w, v ≠ w → ¬ (vectorOrthogonalSixGraph true).Adj v w →
      Fintype.card ((vectorOrthogonalSixGraph true).commonNeighbors v w) = 20
    decide

theorem voSixMinus_isSRG : (vectorOrthogonalSixGraph false).IsSRGWith 64 27 10 12 := by
  constructor
  · decide
  · change ∀ v, (vectorOrthogonalSixGraph false).degree v = 27
    decide
  · decide
  · change ∀ v w, v ≠ w → ¬ (vectorOrthogonalSixGraph false).Adj v w →
      Fintype.card ((vectorOrthogonalSixGraph false).commonNeighbors v w) = 12
    decide

end EPPAIII.Primitive
