import EPPAIII.TwoGraphs.PartialSwitchCycleTelescope

/-!
# Periodic trajectories and the even-cycle obstruction

The abstract XOR telescoping proof is applied to actual iterates
of a partial permutation. If two trajectories return to their
respective starting vertices after n steps, their XOR-sums of
potential values agree. If a trajectory returns to its start
after 2m steps, compare the first and second halves by using
a pair of vertices m steps apart. The pair returns with its
endpoints swapped, so symmetry of the edge indicator forces the
XOR of the potential along the complete even cycle to vanish.

This is the all-order even-cycle compatibility argument in
Section 5.1, without any finite graph enumeration or an
assumed cycle decomposition.
-/

namespace EPPAIII.TwoGraphs

/-- A prefix sum decomposes into the first m terms and the
following n terms. -/
theorem xorPrefix_add (f : ℕ → Bool) (m n : ℕ) :
    xorPrefix f (m + n) =
      Bool.xor (xorPrefix f m)
        (xorPrefix (fun i => f (m + i)) n) := by
  induction n with
  | zero =>
      change xorPrefix f m = Bool.xor (xorPrefix f m) false
      cases h : xorPrefix f m <;> rfl
  | succ n ih =>
      calc
        xorPrefix f (m + (n + 1)) =
          Bool.xor (xorPrefix f (m + n)) (f (m + n)) := by
            rw [Nat.add_succ]
            rfl
        _ = Bool.xor
              (Bool.xor (xorPrefix f m)
                (xorPrefix (fun i => f (m + i)) n))
              (f (m + n)) := by rw [ih]
        _ = Bool.xor (xorPrefix f m)
              (Bool.xor (xorPrefix (fun i => f (m + i)) n)
                (f (m + n))) := by
                  cases a : xorPrefix f m <;>
                    cases b : xorPrefix (fun i => f (m + i)) n <;>
                    cases c : f (m + n) <;> rfl
        _ = Bool.xor (xorPrefix f m)
              (xorPrefix (fun i => f (m + i)) (n + 1)) := rfl

/-- If two directed trajectories of p stay in the finite domain
and return simultaneously to their respective starts, the
total discrepancy on their edge returns to zero, so the
potential sums along the trajectories agree. -/
theorem partial_pair_trajectories_cycle_sums_equal
    {V : Type*}
    (edge : V → V → Bool) (h : V → Bool)
    (p : V → V) (D : Finset V)
    (hDelta : ∀ a ∈ D, ∀ b ∈ D,
      Bool.xor (edge a b) (edge (p a) (p b)) =
        Bool.xor (h a) (h b))
    (x y : ℕ → V)
    (hStepX : ∀ i, x (i + 1) = p (x i))
    (hStepY : ∀ i, y (i + 1) = p (y i))
    (hInX : ∀ i, x i ∈ D)
    (hInY : ∀ i, y i ∈ D)
    (n : ℕ)
    (hCloseX : x n = x 0)
    (hCloseY : y n = y 0) :
    xorPrefix (fun i => h (x i)) n =
      xorPrefix (fun i => h (y i)) n := by
  have hPairs : ∀ i,
      Bool.xor (edge (x i) (y i))
        (edge (x (i + 1)) (y (i + 1))) =
          Bool.xor (h (x i)) (h (y i)) := by
    intro i
    rw [hStepX i,hStepY i]
    exact hDelta (x i) (hInX i) (y i) (hInY i)
  apply pair_cycle_xor_sums_equal edge h x y hPairs n
  rw [hCloseX,hCloseY]

/-- Every even periodic orbit has zero total discrepancy
potential. The two half-trajectories close after m steps
with their endpoints interchanged. -/
theorem partial_even_cycle_potential_zero
    {V : Type*}
    (edge : V → V → Bool)
    (hSym : ∀ a b : V, edge a b = edge b a)
    (h : V → Bool)
    (p : V → V) (D : Finset V)
    (hDelta : ∀ a ∈ D, ∀ b ∈ D,
      Bool.xor (edge a b) (edge (p a) (p b)) =
        Bool.xor (h a) (h b))
    (x : ℕ → V)
    (hStep : ∀ i, x (i + 1) = p (x i))
    (hIn : ∀ i, x i ∈ D)
    (m : ℕ)
    (hClose : x (m + m) = x 0) :
    xorPrefix (fun i => h (x i)) (m + m) = false := by
  let y : ℕ → V := fun i => x (m + i)
  have hStepY : ∀ i, y (i + 1) = p (y i) := by
    intro i
    change x (m + (i + 1)) = p (x (m + i))
    simpa only [Nat.add_succ] using hStep (m + i)
  have hPairs : ∀ i,
      Bool.xor (edge (x i) (y i))
          (edge (x (i + 1)) (y (i + 1))) =
        Bool.xor (h (x i)) (h (y i)) := by
    intro i
    rw [hStep i,hStepY i]
    exact hDelta (x i) (hIn i) (y i) (hIn (m + i))
  have hFirst : x m = y 0 := by simp [y]
  have hSecond : y m = x 0 := by simpa [y] using hClose
  have hHalf := pair_swapped_cycle_xor_sums_equal
    edge hSym h x y hPairs m hFirst hSecond
  have hSplit := xorPrefix_add (fun i => h (x i)) m m
  rw [hSplit]
  change Bool.xor (xorPrefix (fun i => h (x i)) m)
      (xorPrefix (fun i => h (y i)) m) = false
  rw [hHalf]
  cases hh : xorPrefix (fun i => h (y i)) m <;> rfl

end EPPAIII.TwoGraphs
