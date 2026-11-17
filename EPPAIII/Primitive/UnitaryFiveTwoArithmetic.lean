import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.IntervalCases

/-! # Local clique multiplicities in the rank-two unitary graph U₅(2) -/

namespace EPPAIII.Primitive

/-- The order of the automorphism group of a selected disjoint union of
cliques with multiplicities `a,b,c,d` for sizes one through four. -/
def fourCliqueSizesAutOrder (a b c d : ℕ) : ℕ :=
  a.factorial * (2 ^ b * b.factorial) * (6 ^ c * c.factorial) * (24 ^ d * d.factorial)

set_option maxHeartbeats 0 in
set_option maxRecDepth 50000 in
private theorem unitaryFiveTwo_cliqueProfileMin_fin :
    ∀ a b c d : Fin 10, a.val + b.val + c.val + d.val ≤ 9 →
      19 ≤ a.val + 2 * b.val + 3 * c.val + 4 * d.val →
      497664 ≤ fourCliqueSizesAutOrder a.val b.val c.val d.val := by
  decide

/-- If at least nineteen vertices are selected across at most nine cliques
of order four, the local automorphism group order exceeds the published
root-stabilizer order 165888. -/
theorem unitaryFiveTwo_cliqueProfileMin {a b c d : ℕ}
    (hCliques : a + b + c + d ≤ 9) (hSelected : 19 ≤ a + 2 * b + 3 * c + 4 * d) :
    497664 ≤ fourCliqueSizesAutOrder a b c d :=
  unitaryFiveTwo_cliqueProfileMin_fin ⟨a, by omega⟩ ⟨b, by omega⟩
    ⟨c, by omega⟩ ⟨d, by omega⟩ hCliques hSelected

/-- The lower bound is attained by two singletons, two pairs, three triples and one
quadruple. -/
theorem unitaryFiveTwo_cliqueProfileMin_attained :
    2 + 2 + 3 + 1 ≤ 9 ∧ 19 ≤ 2 + 2 * 2 + 3 * 3 + 4 * 1 ∧
      fourCliqueSizesAutOrder 2 2 3 1 = 497664 := by
  decide

end EPPAIII.Primitive
