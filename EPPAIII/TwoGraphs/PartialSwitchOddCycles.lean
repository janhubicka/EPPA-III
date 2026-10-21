import EPPAIII.TwoGraphs.PartialSwitchEvenCycle

/-!
# Synchronization of discrepancy sums on odd cycles

Instead of using lcm, synchronize two odd periods a and b at
their product a*b. Each traversal of the first cycle is then
repeated b times; each traversal of the second is repeated
a times. Both repetition counts are odd, so the corresponding
XOR-prefix sums reduce to one traversal. Pair telescoping at
the common return forces equality of the two cycle sums.

The proof uses explicit block-periodicity hypotheses on the
sequences, so it applies to arbitrary positive odd lengths
without assuming that the orbits are disjoint or minimal.
Deriving the block-periodicity hypotheses from cyclic partial
permutations is a separate small dynamical interface.
-/

namespace EPPAIII.TwoGraphs

/-- The XOR of an n-periodic Boolean sequence over k full
blocks is the XOR of k copies of the first-block XOR. -/
theorem xorPrefix_repeated_blocks
    (f : ℕ → Bool) (period repetitions : ℕ)
    (hBlocks : ∀ k i : ℕ,
      f (period * k + i) = f i) :
    xorPrefix f (period * repetitions) =
      xorPrefix (fun _ : ℕ => xorPrefix f period) repetitions := by
  induction repetitions with
  | zero =>
      change false = false
      rfl
  | succ k ih =>
      have hShift :
          xorPrefix (fun i => f (period * k + i)) period =
            xorPrefix f period := by
        have hf : (fun i => f (period * k + i)) = f := by
          funext i
          exact hBlocks k i
        rw [hf]
      calc
        xorPrefix f (period * (k + 1)) =
            xorPrefix f (period * k + period) := by
              rw [Nat.mul_succ]
        _ = Bool.xor (xorPrefix f (period * k))
              (xorPrefix (fun i => f (period * k + i)) period) :=
                xorPrefix_add f (period * k) period
        _ = Bool.xor
              (xorPrefix (fun _ : ℕ => xorPrefix f period) k)
              (xorPrefix f period) := by rw [ih,hShift]
        _ = xorPrefix (fun _ : ℕ => xorPrefix f period) (k + 1) :=
          rfl

/-- Two adjacent occurrences of a constant bit cancel. -/
private theorem xorPrefix_const_add_two (bit : Bool) (n : ℕ) :
    xorPrefix (fun _ : ℕ => bit) (n + 2) =
      xorPrefix (fun _ : ℕ => bit) n := by
  change Bool.xor
      (Bool.xor (xorPrefix (fun _ : ℕ => bit) n) bit) bit =
        xorPrefix (fun _ : ℕ => bit) n
  cases hv : xorPrefix (fun _ : ℕ => bit) n <;>
    cases bit <;> rfl

/-- XOR of an odd number of copies of a Boolean bit is
that bit. The odd number is written as 2*k+1. -/
theorem xorPrefix_odd_constant (bit : Bool) (k : ℕ) :
    xorPrefix (fun _ : ℕ => bit) (2 * k + 1) = bit := by
  induction k with
  | zero =>
      cases bit <;> rfl
  | succ k ih =>
      have hArithmetic : 2 * (k + 1) + 1 =
          (2 * k + 1) + 2 := by omega
      rw [hArithmetic, xorPrefix_const_add_two, ih]

/-- Two odd periodic trajectories of a partial permutation
have the same discrepancy-potential sum on one full cycle.
Explicit witnesses a=2*k+1 and b=2*l+1 avoid any
divisibility assumptions, using period product a*b. -/
theorem partial_odd_cycles_potential_sums_equal
    {V : Type*}
    (edge : V → V → Bool) (h : V → Bool)
    (p : V → V) (D : Finset V)
    (hDelta : ∀ u ∈ D, ∀ v ∈ D,
      Bool.xor (edge u v) (edge (p u) (p v)) =
        Bool.xor (h u) (h v))
    (x y : ℕ → V)
    (hStepX : ∀ i, x (i + 1) = p (x i))
    (hStepY : ∀ i, y (i + 1) = p (y i))
    (hInX : ∀ i, x i ∈ D)
    (hInY : ∀ i, y i ∈ D)
    (a b k l : ℕ)
    (ha : a = 2 * k + 1) (hb : b = 2 * l + 1)
    (hPeriodX : ∀ j i : ℕ, x (a * j + i) = x i)
    (hPeriodY : ∀ j i : ℕ, y (b * j + i) = y i) :
    xorPrefix (fun i => h (x i)) a =
      xorPrefix (fun i => h (y i)) b := by
  let fx : ℕ → Bool := fun i => h (x i)
  let fy : ℕ → Bool := fun i => h (y i)
  have hxBlocks : ∀ j i, fx (a * j + i) = fx i := by
    intro j i
    exact congrArg h (hPeriodX j i)
  have hyBlocks : ∀ j i, fy (b * j + i) = fy i := by
    intro j i
    exact congrArg h (hPeriodY j i)
  have hCloseX : x (a * b) = x 0 := by
    simpa using hPeriodX b 0
  have hCloseY : y (a * b) = y 0 := by
    simpa [Nat.mul_comm] using hPeriodY a 0
  have hCommon :=
    partial_pair_trajectories_cycle_sums_equal
      edge h p D hDelta x y hStepX hStepY
      hInX hInY (a * b) hCloseX hCloseY
  have hRepetitionsX :
      xorPrefix fx (a * b) =
        xorPrefix (fun _ : ℕ => xorPrefix fx a) b :=
    xorPrefix_repeated_blocks fx a b hxBlocks
  have hRepetitionsY :
      xorPrefix fy (a * b) =
        xorPrefix (fun _ : ℕ => xorPrefix fy b) a := by
    calc
      xorPrefix fy (a * b) =
          xorPrefix fy (b * a) := by rw [Nat.mul_comm a b]
      _ = xorPrefix (fun _ : ℕ => xorPrefix fy b) a :=
        xorPrefix_repeated_blocks fy b a hyBlocks
  have hOddX :
      xorPrefix (fun _ : ℕ => xorPrefix fx a) b =
        xorPrefix fx a := by
    rw [hb]
    exact xorPrefix_odd_constant _ l
  have hOddY :
      xorPrefix (fun _ : ℕ => xorPrefix fy b) a =
        xorPrefix fy b := by
    rw [ha]
    exact xorPrefix_odd_constant _ k
  calc
    xorPrefix (fun i => h (x i)) a =
        xorPrefix (fun _ : ℕ => xorPrefix fx a) b :=
          hOddX.symm
    _ = xorPrefix fx (a * b) := hRepetitionsX.symm
    _ = xorPrefix fy (a * b) := hCommon
    _ = xorPrefix (fun _ : ℕ => xorPrefix fy b) a :=
      hRepetitionsY
    _ = xorPrefix (fun i => h (y i)) b := hOddY

end EPPAIII.TwoGraphs
