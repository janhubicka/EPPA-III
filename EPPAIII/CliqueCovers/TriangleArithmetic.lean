import Mathlib

/-!
# Arithmetic used in the unequal-clique Taylor-double triangle obstruction

The graph-counting argument is recorded separately in
`validation/repair-claims-313-316.tex` and has an executable exhaustive
finite check. This module verifies its algebraic identity and the
inequality obstruction in Lean.

It does NOT claim a proof of the graph-counting formula itself or of
Lemma 3.12 in full.
-/

namespace EPPAIII

/-- The clique-size-dependent contribution to the number of triangles
through a vertex in a Taylor double of disjoint cliques. -/
def doubleTriangleAdjustment (n k : ℤ) : ℤ :=
  (k - 1) * (n - k - 1)

theorem doubleTriangleAdjustment_sub (n a b : ℤ) :
    doubleTriangleAdjustment n a - doubleTriangleAdjustment n b =
      (a - b) * (n - a - b) := by
  unfold doubleTriangleAdjustment
  ring

/-- Different clique sizes produce different triangle counts when
at least one further clique is present. -/
theorem doubleTriangleAdjustment_ne (n a b : ℤ)
    (hab : a ≠ b) (hthird : 0 < n - a - b) :
    doubleTriangleAdjustment n a ≠ doubleTriangleAdjustment n b := by
  intro he
  have hzero : (a - b) * (n - a - b) = 0 := by
    rw [← doubleTriangleAdjustment_sub, he]
    ring
  rcases mul_eq_zero.mp hzero with h | h
  · exact hab (sub_eq_zero.mp h)
  · omega

end EPPAIII
