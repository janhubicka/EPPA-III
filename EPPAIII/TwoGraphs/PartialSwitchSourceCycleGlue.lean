import EPPAIII.TwoGraphs.PartialSwitchCycleClose

/-!
# Switching equations by finite deletion of a source or a cycle arrow

Suppose every nonempty finite subsystem of the partial permutation
has either a source or a closed directed cycle with its final
vertex distinct from all the preceding vertices. Suppose moreover
that the Boolean vertex potential has compatible sum around every
such closed walk.

Strong induction on the set of constrained arrows constructs a
single switching function. At a source, set its Boolean label after
solving the smaller set. At a closed cycle, delete its final arrow,
solve the smaller set, and recover the deleted equation from the
cycle-sum compatibility theorem.

The source-or-cycle property is an *explicit graph-theoretic
hypothesis* in this module, to be derived separately from finiteness
and injectivity; it is not a new axiom.
-/

namespace EPPAIII.TwoGraphs

/-- Every nonempty subsystem either has a source or contains
a removable last arrow on a simple directed cycle. -/
def HasSourceOrRemovableCycle {V : Type*}
    (p : Equiv.Perm V) (D : Finset V) : Prop :=
  ∀ (S : Finset V), S ⊆ D → S.Nonempty →
    (∃ z ∈ S, ∀ y ∈ S, p y ≠ z) ∨
    (∃ (n : ℕ) (x : ℕ → V),
      (∀ i : ℕ, i ≤ n → x i ∈ S) ∧
      (∀ i : ℕ, i ≤ n → x (i + 1) = p (x i)) ∧
      x (n + 1) = x 0 ∧
      (∀ i : ℕ, i < n → x i ≠ x n))

/-- An explicit compatibility interface for Boolean switching
equations on every directed closed walk inside D. -/
def HasCompatibleCycleSums {V : Type*}
    (p : Equiv.Perm V) (D : Finset V)
    (h : V → Bool) (c : Bool) : Prop :=
  ∀ (n : ℕ) (x : ℕ → V),
    (∀ i : ℕ, i ≤ n → x i ∈ D) →
    (∀ i : ℕ, i ≤ n → x (i + 1) = p (x i)) →
    x (n + 1) = x 0 →
    xorPrefix (fun i => h (x i)) (n + 1) =
      xorPrefix (fun _ : ℕ => c) (n + 1)

/-- Construct a global switching function using only
source/cycle deletion and the abstract cycle-sum
compatibility condition. The deleted cycle equation is
recovered, not postulated. -/
theorem vertex_equations_of_source_or_cycle
    {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (D : Finset V)
    (h : V → Bool) (c : Bool)
    (hStructure : HasSourceOrRemovableCycle p D)
    (hCompatible : HasCompatibleCycleSums p D h c) :
    ∃ t : V → Bool,
      ∀ z ∈ D,
        Bool.xor (t z) (t (p z)) = Bool.xor (h z) c := by
  classical
  have aux : ∀ E : Finset V, E ⊆ D →
      ∃ t : V → Bool,
        ∀ z ∈ E,
          Bool.xor (t z) (t (p z)) = Bool.xor (h z) c := by
    intro E
    refine Finset.strongInductionOn E ?_
    intro S ih hSD
    by_cases hS : S.Nonempty
    · rcases hStructure S hSD hS with hSource | hCycle
      · obtain ⟨z,hz,hNoIncoming⟩ := hSource
        have hSmall : S.erase z ⊆ D :=
          (Finset.erase_subset z S).trans hSD
        obtain ⟨t,ht⟩ :=
          ih (S.erase z) (Finset.erase_ssubset hz) hSmall
        let tz : Bool := Bool.xor (Bool.xor (h z) c) (t (p z))
        let T : V → Bool := fun y => if y = z then tz else t y
        refine ⟨T, ?_⟩
        intro y hy
        by_cases hyz : y = z
        · subst y
          have hPz : p z ≠ z := hNoIncoming z hz
          change Bool.xor
            (if z = z then tz else t z)
            (if p z = z then tz else t (p z)) =
              Bool.xor (h z) c
          simp only [if_pos rfl, if_neg hPz]
          dsimp [tz]
          cases hh : h z <;>
            cases hc : c <;>
            cases htpx : t (p z) <;> decide
        · have hySmall : y ∈ S.erase z :=
            Finset.mem_erase.mpr ⟨hyz,hy⟩
          have hPy : p y ≠ z := hNoIncoming y hy
          have hOld := ht y hySmall
          change Bool.xor
            (if y = z then tz else t y)
            (if p y = z then tz else t (p y)) =
              Bool.xor (h y) c
          simpa only [if_neg hyz, if_neg hPy] using hOld
      · obtain ⟨n,x,hIn,hStep,hClose,hDistinct⟩ := hCycle
        have hz : x n ∈ S := hIn n (Nat.le_refl n)
        have hSmall : S.erase (x n) ⊆ D :=
          (Finset.erase_subset (x n) S).trans hSD
        obtain ⟨t,ht⟩ :=
          ih (S.erase (x n)) (Finset.erase_ssubset hz) hSmall
        have hEarlier : ∀ i : ℕ, i < n →
            Bool.xor (t (x i)) (t (x (i + 1))) =
              Bool.xor (h (x i)) c := by
          intro i hi
          have hXi : x i ∈ S := hIn i (Nat.le_of_lt hi)
          have hXiSmall : x i ∈ S.erase (x n) :=
            Finset.mem_erase.mpr ⟨hDistinct i hi,hXi⟩
          have hh := ht (x i) hXiSmall
          rw [← hStep i (Nat.le_of_lt hi)] at hh
          exact hh
        have hCycleCompatible :
            xorPrefix (fun i => h (x i)) (n + 1) =
              xorPrefix (fun _ : ℕ => c) (n + 1) := by
          apply hCompatible n x
          · intro i hi
            exact hSD (hIn i hi)
          · exact hStep
          · exact hClose
        have hLast := last_cycle_equation_of_compatible_sum
          x t h c n hClose hCycleCompatible hEarlier
        rw [hStep n (Nat.le_refl n)] at hLast
        refine ⟨t, ?_⟩
        intro z hzS
        by_cases hzEq : z = x n
        · subst z
          exact hLast
        · exact ht z (Finset.mem_erase.mpr ⟨hzEq,hzS⟩)
    · refine ⟨fun _ => false, ?_⟩
      intro z hz
      exact (hS ⟨z,hz⟩).elim
  exact aux D (Finset.Subset.rfl)

end EPPAIII.TwoGraphs
