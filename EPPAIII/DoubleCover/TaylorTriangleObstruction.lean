import EPPAIII.DoubleCover.TriangleTransport
import EPPAIII.DoubleCover.TaylorTriangleScore

/-!
# The final numerical obstruction, conditional on the graph-level formula

Suppose that in a vertex-transitive host the number of ordered
triangles through two vertices is twice the Taylor score
T(k)=C+(k-1)(n-k-1), for their respective base clique sizes.

Actual graph transitivity makes the ordered counts equal.
The verified score-difference factorisation then forces equal
clique sizes whenever the remaining base components have positive
total size.

The hypotheses below explicitly contain the as-yet-unproved
graph-level formula. This theorem is not an unconditional
classification of Taylor doubles or a proof of Lemma 3.12.
-/

namespace EPPAIII.DoubleCover

/-- Under the expected exact graph-level count, unequal clique
sizes with another nonempty component contradict actual vertex
transitivity. This isolates precisely the missing count bridge. -/
theorem unequal_taylor_scores_contradict_host_transitivity
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (hTrans : BlockSystems.IsVertexTransitive H)
    (u v : W) (background n a b : ℤ)
    (hCountU :
      ((orderedTrianglePairsAt H u).card : ℤ) =
        2 * taylorTriangleScore background n a)
    (hCountV :
      ((orderedTrianglePairsAt H v).card : ℤ) =
        2 * taylorTriangleScore background n b)
    (hDifferent : a ≠ b)
    (hThird : 0 < n - a - b) : False := by
  have hNatural :
      (orderedTrianglePairsAt H u).card =
        (orderedTrianglePairsAt H v).card :=
    orderedTrianglePairsAt_card_transitive H hTrans u v
  have hInteger :
      ((orderedTrianglePairsAt H u).card : ℤ) =
        ((orderedTrianglePairsAt H v).card : ℤ) := by
    exact_mod_cast hNatural
  have hTwice :
      2 * taylorTriangleScore background n a =
        2 * taylorTriangleScore background n b :=
    hCountU.symm.trans (hInteger.trans hCountV)
  have hEqual :
      taylorTriangleScore background n a =
        taylorTriangleScore background n b := by
    nlinarith
  exact
    (taylorTriangleScore_ne_of_third_component
      background n a b hDifferent hThird) hEqual

end EPPAIII.DoubleCover
