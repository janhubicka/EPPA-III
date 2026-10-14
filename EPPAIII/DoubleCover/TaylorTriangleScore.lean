import Mathlib

/-!
# Case 2: the triangle-score separation in a Taylor double

For the Taylor double of a disjoint union of cliques of total
order n, the paper-level triangle-count calculation gives

    T_i = C + (k_i-1)(n-k_i-1),

where C is independent of the clique index i. Its difference
between two indices factors as

    T_i - T_j = (k_i-k_j)(n-k_i-k_j).

This file checks that precise algebraic identity over integers,
and proves that unequal clique orders force unequal scores
whenever there is a nonempty third component.

**Scope boundary:** The graph-theoretic lemma identifying the
actual number of triangles through a vertex with this score is
not yet established in Lean. No claim that the full Case-2
vertex-transitivity obstruction has been verified is made here.
-/

namespace EPPAIII.DoubleCover

/-- The index-dependent term in the Taylor-double triangle count. -/
def taylorTriangleLocalScore (n k : ℤ) : ℤ :=
  (k - 1) * (n - k - 1)

/-- The proposed triangle count, including an index-independent
background term. The latter cancels when two indices are compared. -/
def taylorTriangleScore (background n k : ℤ) : ℤ :=
  background + taylorTriangleLocalScore n k

/-- Exact factorization of the triangle-count difference. -/
theorem taylorTriangleScore_difference (background n a b : ℤ) :
    taylorTriangleScore background n a -
      taylorTriangleScore background n b =
        (a - b) * (n - a - b) := by
  unfold taylorTriangleScore taylorTriangleLocalScore
  ring

/-- Two unequal clique orders give different scores whenever
the other clique components have positive total order. -/
theorem taylorTriangleScore_ne_of_third_component
    (background n a b : ℤ)
    (hab : a ≠ b) (hRest : 0 < n - a - b) :
    taylorTriangleScore background n a ≠
      taylorTriangleScore background n b := by
  intro hEq
  have hProduct : (a - b) * (n - a - b) = 0 := by
    calc
      (a - b) * (n - a - b) =
          taylorTriangleScore background n a -
            taylorTriangleScore background n b :=
        (taylorTriangleScore_difference background n a b).symm
      _ = 0 := sub_eq_zero.mpr hEq
  rcases mul_eq_zero.mp hProduct with hA | hB
  · exact hab (sub_eq_zero.mp hA)
  · exact (ne_of_gt hRest) hB

end EPPAIII.DoubleCover
