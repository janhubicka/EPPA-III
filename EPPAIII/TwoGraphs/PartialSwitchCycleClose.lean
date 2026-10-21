import EPPAIII.TwoGraphs.PartialSwitchOddCycles
import EPPAIII.TwoGraphs.PartialSwitchPaths

/-!
# Closing a deleted switching equation around a directed cycle

The Boolean switching equations form a partial functional graph.
If we remove the equation at one chosen cycle vertex, we can
solve the remaining equations by induction; the removed equation
then follows from compatibility of the complete cycle XOR-sum.

This file certifies that last implication without assuming any
particular cycle length or how the remaining equations were solved.
In particular it proves all Boolean cancellation identities, rather
than treating the final equation as a computational check.

Finite orbit extraction and the global choice of the constant c
remain separate obligations for the full partial-switching lemma.
-/

namespace EPPAIII.TwoGraphs

/-- XOR-prefix sums respect equality of the summands on an
initial segment. -/
theorem xorPrefix_congr_on_initial
    (f g : ℕ → Bool) (n : ℕ)
    (h : ∀ i : ℕ, i < n → f i = g i) :
    xorPrefix f n = xorPrefix g n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change Bool.xor (xorPrefix f k) (f k) =
        Bool.xor (xorPrefix g k) (g k)
      rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)),
        h k (Nat.lt_succ_self k)]

/-- Prefix XOR distributes over pointwise XOR. -/
theorem xorPrefix_pointwise_xor
    (f g : ℕ → Bool) (n : ℕ) :
    xorPrefix (fun i => Bool.xor (f i) (g i)) n =
      Bool.xor (xorPrefix f n) (xorPrefix g n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change
        Bool.xor
          (xorPrefix (fun i => Bool.xor (f i) (g i)) k)
          (Bool.xor (f k) (g k)) =
        Bool.xor (Bool.xor (xorPrefix f k) (f k))
          (Bool.xor (xorPrefix g k) (g k))
      rw [ih]
      cases a : xorPrefix f k <;>
        cases b : xorPrefix g k <;>
        cases c : f k <;>
        cases d : g k <;> rfl

/-- The XOR of consecutive differences along any finite
sequence is its endpoint difference. -/
theorem xorPrefix_successive_differences
    (a : ℕ → Bool) (n : ℕ) :
    xorPrefix (fun i => Bool.xor (a i) (a (i + 1))) n =
      Bool.xor (a 0) (a n) := by
  induction n with
  | zero =>
      cases h : a 0 <;> rfl
  | succ k ih =>
      change
        Bool.xor
          (xorPrefix (fun i => Bool.xor (a i) (a (i + 1))) k)
          (Bool.xor (a k) (a (k + 1))) =
        Bool.xor (a 0) (a (k + 1))
      rw [ih]
      cases h0 : a 0 <;>
        cases hk : a k <;>
        cases hk1 : a (k + 1) <;> rfl

/-- One missing final equation on a closed cycle is forced
by the equations at all earlier vertices and equality of the
complete h-sum with the complete constant-c sum.

The sequence x_0,...,x_n,x_(n+1)=x_0 need not consist of
different vertices; that stronger condition is relevant only
when one wants to infer the earlier equations from deleting
one specific vertex of the original domain. -/
theorem last_cycle_equation_of_compatible_sum
    {V : Type*}
    (x : ℕ → V) (t h : V → Bool) (c : Bool)
    (n : ℕ)
    (hClose : x (n + 1) = x 0)
    (hCompatible :
      xorPrefix (fun i => h (x i)) (n + 1) =
        xorPrefix (fun _ : ℕ => c) (n + 1))
    (hEarlier : ∀ i : ℕ, i < n →
      Bool.xor (t (x i)) (t (x (i + 1))) =
        Bool.xor (h (x i)) c) :
    Bool.xor (t (x n)) (t (x (n + 1))) =
      Bool.xor (h (x n)) c := by
  let f : ℕ → Bool := fun i =>
    Bool.xor (t (x i)) (t (x (i + 1)))
  let g : ℕ → Bool := fun i =>
    Bool.xor (h (x i)) c
  have hPrefix : xorPrefix f n = xorPrefix g n :=
    xorPrefix_congr_on_initial f g n hEarlier
  have hfZero : xorPrefix f (n + 1) = false := by
    change
      xorPrefix (fun i => Bool.xor
        (t (x i)) (t (x (i + 1)))) (n + 1) = false
    rw [xorPrefix_successive_differences
      (fun i => t (x i)) (n + 1), hClose]
    cases hb : t (x 0) <;> rfl
  have hgZero : xorPrefix g (n + 1) = false := by
    change
      xorPrefix (fun i => Bool.xor (h (x i)) c) (n + 1) =
        false
    rw [xorPrefix_pointwise_xor
      (fun i => h (x i)) (fun _ : ℕ => c) (n + 1),
      hCompatible]
    cases hb : xorPrefix (fun _ : ℕ => c) (n + 1) <;> rfl
  have hFull : xorPrefix f (n + 1) =
      xorPrefix g (n + 1) := hfZero.trans hgZero.symm
  change Bool.xor (xorPrefix f n) (f n) =
    Bool.xor (xorPrefix g n) (g n) at hFull
  rw [hPrefix] at hFull
  change f n = g n
  cases hb : xorPrefix g n <;>
    cases hf : f n <;>
    cases hg : g n <;> simp_all [Bool.xor]

end EPPAIII.TwoGraphs
