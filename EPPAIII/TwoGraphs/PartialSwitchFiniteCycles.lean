import EPPAIII.TwoGraphs.PartialSwitchSourceCycleGlue

/-!
# Finite partial permutation graphs: a source or a removable cycle

If every point of a finite subsystem has a predecessor in that
subsystem, injectivity and finite cardinality imply that the
permutation also maps the subsystem into itself. Any orbit then
has a smallest positive return period, giving a directed cycle
whose final vertex does not occur earlier.

This is the exact combinatorial decomposition needed by the
strong-induction switching-equation solver. It avoids any
external graph classification, and makes no choice of a
coherent family of partial automorphism extensions.
-/

namespace EPPAIII.TwoGraphs

/-- Every point of a finite permutation lies on a positive
periodic orbit. Orient its traversal to finish at the chosen
point z; minimality makes that final point new among the
earlier vertices. -/
theorem permutation_simple_positive_cycle
    {V : Type*} [Fintype V]
    (p : Equiv.Perm V) (z : V) :
    ∃ (n : ℕ) (x : ℕ → V),
      x 0 = p z ∧
      (∀ i : ℕ, x (i + 1) = p (x i)) ∧
      x n = z ∧
      x (n + 1) = x 0 ∧
      (∀ i : ℕ, i < n → x i ≠ x n) := by
  classical
  let N : ℕ := Fintype.card (Equiv.Perm V)
  have hN : 0 < N := Fintype.card_pos
  have hOrder : p ^ N = 1 := pow_card_eq_one
  have hReturn : (p.toFun^[N]) z = z := by
    have hh := congrArg (fun q : Equiv.Perm V => q z) hOrder
    simpa [pow_apply_eq_iterate] using hh
  let P : ℕ → Prop :=
    fun k => 0 < k ∧ (p.toFun^[k]) z = z
  have hExists : ∃ k, P k := ⟨N,hN,hReturn⟩
  let m : ℕ := Nat.find hExists
  have hM : P m := Nat.find_spec hExists
  let n : ℕ := m - 1
  have hm : m = n + 1 := by
    dsimp [n]
    omega
  let x : ℕ → V := fun i => (p.toFun^[i + 1]) z
  have hStep : ∀ i : ℕ,
      x (i + 1) = p (x i) := by
    intro i
    change (p.toFun^[i + 1 + 1]) z =
      p ((p.toFun^[i + 1]) z)
    simpa only [Nat.add_assoc] using
      (Function.iterate_succ_apply' p.toFun (i + 1) z)
  have hEnd : x n = z := by
    change (p.toFun^[n + 1]) z = z
    rw [←hm]
    exact hM.2
  have hZero : x 0 = p z := by
    change (p.toFun^[0 + 1]) z = p z
    simp [Function.iterate_succ_apply']
  have hClose : x (n + 1) = x 0 := by
    calc
      x (n + 1) = p (x n) := hStep n
      _ = p z := by rw [hEnd]
      _ = x 0 := hZero.symm
  have hDistinct : ∀ i : ℕ, i < n → x i ≠ x n := by
    intro i hi hEq
    have hSmall : i + 1 < m := by
      dsimp [n] at hi
      omega
    have hNot : ¬ P (i + 1) := Nat.find_min hExists hSmall
    apply hNot
    refine ⟨by omega, ?_⟩
    change (p.toFun^[i + 1]) z = z
    exact hEq.trans hEnd
  exact ⟨n,x,hZero,hStep,hEnd,hClose,hDistinct⟩

/-- Every finite partial permutation graph has either a source
or a removable cycle on every nonempty subsystem.
This discharges the *structural* assumption of the
source-or-cycle switching solver in full generality. -/
theorem finite_permutation_has_source_or_removable_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (D : Finset V) :
    HasSourceOrRemovableCycle p D := by
  classical
  intro S hSD hS
  by_cases hSource : ∃ z ∈ S, ∀ y ∈ S, p y ≠ z
  · exact Or.inl hSource
  · right
    have hPrevious (z : V) (hz : z ∈ S) :
        p.symm z ∈ S := by
      by_contra hNot
      apply hSource
      refine ⟨z,hz,?_⟩
      intro y hy hpy
      have hyEq : y = p.symm z := by
        apply p.injective
        simpa using hpy
      exact hNot (hyEq ▸ hy)
    have hBackSubset :
        S.image (fun z : V => p.symm z) ⊆ S := by
      intro w hw
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
      exact hPrevious z hz
    have hCard :
        (S.image (fun z : V => p.symm z)).card = S.card := by
      exact Finset.card_image_iff.mpr p.symm.injective.injOn
    have hBackEq :
        S.image (fun z : V => p.symm z) = S :=
      Finset.eq_of_subset_of_card_le hBackSubset hCard.symm.le
    have hForward (z : V) (hz : z ∈ S) : p z ∈ S := by
      have hzImage :
          z ∈ S.image (fun y : V => p.symm y) := by
        rw [hBackEq]
        exact hz
      obtain ⟨y,hy,hyz⟩ := Finset.mem_image.mp hzImage
      have hpy : p z = y := by
        simpa using (congrArg p hyz).symm
      exact hpy.symm ▸ hy
    obtain ⟨z,hz⟩ := hS
    obtain ⟨n,x,hZero,hStep,hEnd,hClose,hDistinct⟩ :=
      permutation_simple_positive_cycle p z
    have hIn : ∀ i : ℕ, x i ∈ S := by
      intro i
      induction i with
      | zero =>
          rw [hZero]
          exact hForward z hz
      | succ i ih =>
          rw [hStep i]
          exact hForward (x i) ih
    exact ⟨n,x,
      (fun i _ => hIn i),
      (fun i _ => hStep i),
      hClose,hDistinct⟩

end EPPAIII.TwoGraphs
