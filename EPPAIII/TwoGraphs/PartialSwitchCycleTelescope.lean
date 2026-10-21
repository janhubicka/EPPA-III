import EPPAIII.TwoGraphs.PartialAutomorphismParity

/-!
# Telescoping discrepancy along two directed trajectories

This is the reusable Boolean calculation needed in the cyclic
part of Section 5.1's partial two-graph switching lemma.

If a symmetric edge indicator changes from step i to i+1 by
h(x_i) XOR h(y_i), the sum of the h-values on the two
trajectories agrees whenever the endpoint edge returns to
the initial unordered edge. Both the ordinary return and
the swapped-endpoint return are covered.

No finiteness, cycle decomposition, graph classification or
external Mallows--Sloane theorem is used in these lemmas.
-/

namespace EPPAIII.TwoGraphs

/-- XOR of the first n values of a Boolean sequence. -/
def xorPrefix (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => Bool.xor (xorPrefix f n) (f n)

/-- Elementary cancellation of the repeated intermediate term. -/
private theorem xor_chain (a b c : Bool) :
    Bool.xor a c =
      Bool.xor (Bool.xor a b) (Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- Rearrange four XOR summands to collect the trajectories. -/
private theorem xor_shuffle (a b c d : Bool) :
    Bool.xor (Bool.xor a b) (Bool.xor c d) =
      Bool.xor (Bool.xor a c) (Bool.xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- If successive pair discrepancies split as one-vertex
labels, the entire discrepancy telescopes to the XOR of
those labels along each trajectory. -/
theorem pair_discrepancy_telescopes
    {V : Type*}
    (edge : V → V → Bool) (h : V → Bool)
    (x y : ℕ → V)
    (hStep : ∀ i : ℕ,
      Bool.xor (edge (x i) (y i))
          (edge (x (i + 1)) (y (i + 1))) =
        Bool.xor (h (x i)) (h (y i)))
    (n : ℕ) :
    Bool.xor (edge (x 0) (y 0)) (edge (x n) (y n)) =
      Bool.xor (xorPrefix (fun i => h (x i)) n)
        (xorPrefix (fun i => h (y i)) n) := by
  induction n with
  | zero =>
      change Bool.xor (edge (x 0) (y 0)) (edge (x 0) (y 0)) =
        Bool.xor false false
      cases he : edge (x 0) (y 0) <;> rfl
  | succ n ih =>
      calc
        Bool.xor (edge (x 0) (y 0))
          (edge (x (n + 1)) (y (n + 1))) =
            Bool.xor
              (Bool.xor (edge (x 0) (y 0)) (edge (x n) (y n)))
              (Bool.xor (edge (x n) (y n))
                (edge (x (n + 1)) (y (n + 1)))) :=
                  xor_chain _ _ _
        _ = Bool.xor
              (Bool.xor (xorPrefix (fun i => h (x i)) n)
                (xorPrefix (fun i => h (y i)) n))
              (Bool.xor (h (x n)) (h (y n))) := by
                rw [ih, hStep n]
        _ = Bool.xor
              (Bool.xor (xorPrefix (fun i => h (x i)) n) (h (x n)))
              (Bool.xor (xorPrefix (fun i => h (y i)) n) (h (y n))) :=
                xor_shuffle _ _ _ _
        _ = Bool.xor
              (xorPrefix (fun i => h (x i)) (n + 1))
              (xorPrefix (fun i => h (y i)) (n + 1)) := rfl

/-- A Boolean XOR is zero exactly when the summands agree. -/
private theorem xor_eq_of_false (a b : Bool)
    (h : Bool.xor a b = false) : a = b := by
  cases a <;> cases b <;> simp_all [Bool.xor]

/-- If the final ordered pair has the same edge indicator as
the initial pair, the two trajectory sums agree. -/
theorem pair_cycle_xor_sums_equal
    {V : Type*}
    (edge : V → V → Bool) (h : V → Bool)
    (x y : ℕ → V)
    (hStep : ∀ i : ℕ,
      Bool.xor (edge (x i) (y i))
          (edge (x (i + 1)) (y (i + 1))) =
        Bool.xor (h (x i)) (h (y i)))
    (n : ℕ)
    (hReturn : edge (x n) (y n) = edge (x 0) (y 0)) :
    xorPrefix (fun i => h (x i)) n =
      xorPrefix (fun i => h (y i)) n := by
  have hTotal := pair_discrepancy_telescopes
    edge h x y hStep n
  have hZero :
      Bool.xor (xorPrefix (fun i => h (x i)) n)
        (xorPrefix (fun i => h (y i)) n) = false := by
    rw [←hTotal, hReturn]
    cases he : edge (x 0) (y 0) <;> rfl
  exact xor_eq_of_false _ _ hZero

/-- Swapping the two endpoints also closes the unordered
edge whenever the edge indicator is symmetric. This is the
pair-telescoping identity used for half-turns of even cycles. -/
theorem pair_swapped_cycle_xor_sums_equal
    {V : Type*}
    (edge : V → V → Bool)
    (hSym : ∀ a b : V, edge a b = edge b a)
    (h : V → Bool) (x y : ℕ → V)
    (hStep : ∀ i : ℕ,
      Bool.xor (edge (x i) (y i))
          (edge (x (i + 1)) (y (i + 1))) =
        Bool.xor (h (x i)) (h (y i)))
    (n : ℕ)
    (hx : x n = y 0) (hy : y n = x 0) :
    xorPrefix (fun i => h (x i)) n =
      xorPrefix (fun i => h (y i)) n := by
  apply pair_cycle_xor_sums_equal edge h x y hStep n
  rw [hx, hy]
  exact hSym (y 0) (x 0)

end EPPAIII.TwoGraphs
