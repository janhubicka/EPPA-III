import Mathlib

/-!
# A regular symmetric matrix has no zero principal block larger than half

This is the combinatorial counting heart of the true-twin quotient
argument in the zero-partial case of Lemma 3.7.

For a finite symmetric matrix A of natural numbers with a common,
strictly positive row sum d, any coordinate set S on which all entries
of A vanish has size at most half the index set. The proof counts the
weighted edges crossing S and its complement twice:
  |S|*d = cross(S,S^c) = cross(S^c,S) ≤ |S^c|*d.

This weighted statement deliberately avoids reliance on a quotient
graph construction. For a positive-degree regular graph take
A(u,v) = 1 if adjacent and 0 otherwise; the resulting statement is
the standard independence bound α(Q) ≤ |Q|/2.
-/

namespace EPPAIII.CliqueCovers

/-- Double-counting a zero principal block in a symmetric, positive
row-regular nonnegative integer matrix. -/
theorem regular_symmetric_zero_block_le_half {V : Type*}
    [Fintype V]
    (A : V → V → ℕ) (S : Finset V) (d : ℕ)
    (hSym : ∀ u v : V, A u v = A v u)
    (hRegular : ∀ u : V, (∑ v : V, A u v) = d)
    (hZero : ∀ u ∈ S, ∀ v ∈ S, A u v = 0)
    (hd : 0 < d) :
    2 * S.card ≤ Fintype.card V := by
  classical
  have hSplit (u : V) :
      (∑ v ∈ S, A u v) + (∑ v ∈ Sᶜ, A u v) = d := by
    calc
      (∑ v ∈ S, A u v) + (∑ v ∈ Sᶜ, A u v) =
          ∑ v : V, A u v := by
            simpa using
              (Finset.sum_add_sum_compl S (fun v => A u v))
      _ = d := hRegular u
  have hInside (u : V) (hu : u ∈ S) :
      (∑ v ∈ S, A u v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact hZero u hu v hv
  have hLeft (u : V) (hu : u ∈ S) :
      (∑ v ∈ Sᶜ, A u v) = d := by
    have h := hSplit u
    rw [hInside u hu, zero_add] at h
    exact h
  have hCross :
      (∑ u ∈ S, ∑ v ∈ Sᶜ, A u v) =
        (∑ v ∈ Sᶜ, ∑ u ∈ S, A v u) := by
    calc
      (∑ u ∈ S, ∑ v ∈ Sᶜ, A u v) =
          (∑ u ∈ S, ∑ v ∈ Sᶜ, A v u) := by
            apply Finset.sum_congr rfl
            intro u _
            apply Finset.sum_congr rfl
            intro v _
            exact hSym u v
      _ = (∑ v ∈ Sᶜ, ∑ u ∈ S, A v u) :=
        Finset.sum_comm
  have hFullS :
      (∑ u ∈ S, ∑ v ∈ Sᶜ, A u v) = S.card * d := by
    calc
      (∑ u ∈ S, ∑ v ∈ Sᶜ, A u v) =
          (∑ u ∈ S, d) := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hLeft u hu
      _ = S.card * d := by simp
  have hUpperRow (v : V) :
      (∑ u ∈ S, A v u) ≤ d := by
    have h := hSplit v
    omega
  have hMul : S.card * d ≤ Sᶜ.card * d := by
    calc
      S.card * d = (∑ u ∈ S, ∑ v ∈ Sᶜ, A u v) := hFullS.symm
      _ = (∑ v ∈ Sᶜ, ∑ u ∈ S, A v u) := hCross
      _ ≤ (∑ v ∈ Sᶜ, d) := by
        apply Finset.sum_le_sum
        intro v _
        exact hUpperRow v
      _ = Sᶜ.card * d := by simp
  have hLe : S.card ≤ Sᶜ.card :=
    Nat.le_of_mul_le_mul_right hMul hd
  have hTotal : S.card + Sᶜ.card = Fintype.card V :=
    Finset.card_add_card_compl S
  omega

end EPPAIII.CliqueCovers
