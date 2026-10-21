import EPPAIII.TwoGraphs.PartialSwitchFiniteCycles

/-!
# A common switching bit compatible with every closed cycle

The pair-discrepancy formula forces zero XOR-sum around an even
cycle and the same XOR-sum around every odd cycle. We therefore
choose one global bit c: the sum on any odd closed walk when one
exists, or false otherwise.

Compatibility is proved for every globally periodic directed
trajectory, including repeated traversals, rather than just a
chosen decomposition into minimal cycles. Consequently it is the
exact input needed by the source-or-cycle switching induction.
No new mathematical hypotheses beyond the discrepancy formula.
-/

namespace EPPAIII.TwoGraphs

/-- The XOR of an even number of copies of a constant
Boolean value is false. -/
theorem xorPrefix_even_constant (c : Bool) (k : ℕ) :
    xorPrefix (fun _ : ℕ => c) (k + k) = false := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hLen : (k + 1) + (k + 1) = (k + k) + 2 := by omega
      rw [hLen]
      change Bool.xor
        (Bool.xor (xorPrefix (fun _ : ℕ => c) (k + k)) c) c =
          false
      rw [ih]
      cases c <;> rfl

/-- The existence of a directed closed walk of odd positive
length wholly contained in the constrained domain. -/
def HasOddClosedWalk {V : Type*}
    (p : Equiv.Perm V) (D : Finset V) : Prop :=
  ∃ (k : ℕ) (x : ℕ → V),
    (∀ i : ℕ, x i ∈ D) ∧
    (∀ i : ℕ, x (i + 1) = p (x i)) ∧
    x (2 * k + 1) = x 0

/-- Any symmetric pair-edge discrepancy potential admits ONE
Boolean constant c satisfying the necessary cycle-sum condition
for every directed closed walk. Both even and odd lengths are
handled without a minimality or disjointness hypothesis. -/
theorem exists_globally_compatible_cycle_bit
    {V : Type*}
    (edge : V → V → Bool)
    (hSym : ∀ x y : V, edge x y = edge y x)
    (h : V → Bool) (p : Equiv.Perm V) (D : Finset V)
    (hDelta : ∀ x ∈ D, ∀ y ∈ D,
      Bool.xor (edge x y) (edge (p x) (p y)) =
        Bool.xor (h x) (h y)) :
    ∃ c : Bool, HasCompatibleCycleSums p D h c := by
  classical
  by_cases hOdd : HasOddClosedWalk p D
  · obtain ⟨j,y,hYin,hYstep,hYreturn⟩ := hOdd
    let c : Bool := xorPrefix (fun i => h (y i)) (2 * j + 1)
    refine ⟨c, ?_⟩
    intro n x hXin hXstep hXreturn
    let k : ℕ := (n + 1) / 2
    rcases Nat.mod_two_eq_zero_or_one (n + 1) with heven | hodd
    · have hLen : n + 1 = k + k := by
        dsimp [k]
        omega
      have hReturnEven : x (k + k) = x 0 := by
        simpa only [←hLen] using hXreturn
      have hSumZero :=
        partial_even_cycle_potential_zero
          edge hSym h p D hDelta x hXstep hXin
          k hReturnEven
      calc
        xorPrefix (fun i => h (x i)) (n + 1) =
            xorPrefix (fun i => h (x i)) (k + k) := by rw [hLen]
        _ = false := hSumZero
        _ = xorPrefix (fun _ : ℕ => c) (n + 1) := by
          rw [hLen]
          exact (xorPrefix_even_constant c k).symm
    · have hLen : n + 1 = 2 * k + 1 := by
        dsimp [k]
        omega
      have hSumEq :
          xorPrefix (fun i => h (y i)) (2 * j + 1) =
            xorPrefix (fun i => h (x i)) (n + 1) :=
        partial_odd_cycles_potential_equal_of_returns
          edge h p D hDelta y x
          hYstep hXstep hYin hXin
          (2 * j + 1) (n + 1) j k
          rfl hLen hYreturn hXreturn
      calc
        xorPrefix (fun i => h (x i)) (n + 1) = c := hSumEq.symm
        _ = xorPrefix (fun _ : ℕ => c) (n + 1) := by
          rw [hLen]
          exact (xorPrefix_odd_constant c k).symm
  · refine ⟨false, ?_⟩
    intro n x hXin hXstep hXreturn
    let k : ℕ := (n + 1) / 2
    have hEven : (n + 1) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (n + 1) with heven | hodd
      · exact heven
      · exfalso
        apply hOdd
        have hLen : n + 1 = 2 * k + 1 := by
          dsimp [k]
          omega
        refine ⟨k,x,hXin,hXstep, ?_⟩
        simpa only [← hLen] using hXreturn
    have hLen : n + 1 = k + k := by
      dsimp [k]
      omega
    have hReturnEven : x (k + k) = x 0 := by
      simpa only [← hLen] using hXreturn
    have hSumZero :=
      partial_even_cycle_potential_zero
        edge hSym h p D hDelta x hXstep hXin
        k hReturnEven
    calc
      xorPrefix (fun i => h (x i)) (n + 1) =
          xorPrefix (fun i => h (x i)) (k + k) := by rw [hLen]
      _ = false := hSumZero
      _ = xorPrefix (fun _ : ℕ => false) (n + 1) := by
        rw [hLen]
        exact (xorPrefix_even_constant false k).symm

end EPPAIII.TwoGraphs
