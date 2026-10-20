import EPPAIII.CliqueCovers.TwinQuotientCount
import EPPAIII.CliqueCovers.TwinClassTransport
import Mathlib

/-!
# Counting the occupied true-twin quotient classes

The selected base can meet each host twin class in at most the
common class size t. Therefore |G| ≤ t times the number of
occupied quotient classes. If the quotient is positively regular,
those occupied classes form an independent set of size at most
half the quotient order. Double-counting forces equality in both
bounds. The quotient regularity and independence hypotheses
are handled in separate formal modules.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- A finite map with fibres of size at most t has a domain of
size at most t times the size of its image. -/
theorem finite_image_fibre_capacity
    {V Q : Type*} [Fintype V] [Fintype Q]
    [DecidableEq V] [DecidableEq Q]
    (f : V → Q) (t : ℕ)
    (hFib : ∀ q : Q,
      ((Finset.univ : Finset V).filter (fun v => f v = q)).card ≤ t) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).image f).card * t := by
  classical
  let I : Finset Q := (Finset.univ : Finset V).image f
  let fibre (q : Q) : Finset V :=
    (Finset.univ : Finset V).filter (fun v => f v = q)
  have hZero (q : Q) (hq : q ∉ I) : (fibre q).card = 0 := by
    by_contra hn
    have hp : 0 < (fibre q).card := Nat.pos_of_ne_zero hn
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hp
    have hvq : f v = q := (Finset.mem_filter.mp hv).2
    exact hq (Finset.mem_image.mpr
      ⟨v, Finset.mem_univ _, hvq⟩)
  have hCount :
      Fintype.card V = ∑ q : Q, (fibre q).card := by
    simpa [fibre] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset V))
        (t := (Finset.univ : Finset Q))
        (f := f) (by intro _ _; simp))
  have hSubset :
      (∑ q ∈ I, (fibre q).card) =
        (∑ q : Q, (fibre q).card) := by
    apply Finset.sum_subset (Finset.subset_univ I)
    intro q _ hq
    exact hZero q hq
  have hBound :
      (∑ q ∈ I, (fibre q).card) ≤
        (∑ _q ∈ I, t) := by
    apply Finset.sum_le_sum
    intro q _
    exact hFib q
  calc
    Fintype.card V = ∑ q : Q, (fibre q).card := hCount
    _ = ∑ q ∈ I, (fibre q).card := hSubset.symm
    _ ≤ ∑ _q ∈ I, t := hBound
    _ = I.card * t := by simp

/-- Each selected fibre inside one quotient class injects into
the host true-twin class represented by that quotient vertex. -/
theorem selected_twin_fibre_le_class
    {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph W) [DecidableEq (ClosedTwinQuotient H)]
    (e : V ↪ W) (w : W) :
    ((Finset.univ : Finset V).filter
       (fun v =>
         (Quotient.mk (closedTwinSetoid H) (e v) :
           ClosedTwinQuotient H) =
         Quotient.mk (closedTwinSetoid H) w)).card ≤
       (closedTwinClass H w).card := by
  classical
  let S : Finset V :=
    (Finset.univ : Finset V).filter
      (fun v =>
        (Quotient.mk (closedTwinSetoid H) (e v) :
          ClosedTwinQuotient H) =
        Quotient.mk (closedTwinSetoid H) w)
  have hSubset : S.image (fun v => e v) ⊆
      closedTwinClass H w := by
    intro u hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    have hEq :
        (Quotient.mk (closedTwinSetoid H) (e v) :
          ClosedTwinQuotient H) =
        Quotient.mk (closedTwinSetoid H) w :=
      (Finset.mem_filter.mp hv).2
    have hTwin : SameClosedNeighbourhood H (e v) w :=
      Quotient.exact hEq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hTwin.symm⟩
  calc
    S.card = (S.image (fun v => e v)).card :=
      (Finset.card_image_of_injective S e.injective).symm
    _ ≤ (closedTwinClass H w).card := Finset.card_le_card hSubset

/-- A uniform true-twin class size t bounds each selected
fibre over the canonical quotient. -/
theorem selected_twin_quotient_fibre_capacity
    {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph W) [DecidableEq (ClosedTwinQuotient H)]
    (e : V ↪ W) (t : ℕ)
    (hUniform : ∀ w : W, (closedTwinClass H w).card = t)
    (z : ClosedTwinQuotient H) :
    ((Finset.univ : Finset V).filter
      (fun v =>
        (Quotient.mk (closedTwinSetoid H) (e v) :
          ClosedTwinQuotient H) = z)).card ≤ t := by
  classical
  induction z using Quotient.inductionOn with
  | _ w =>
    calc
      ((Finset.univ : Finset V).filter
        (fun v =>
          (Quotient.mk (closedTwinSetoid H) (e v) :
            ClosedTwinQuotient H) =
          Quotient.mk (closedTwinSetoid H) w)).card ≤
          (closedTwinClass H w).card :=
        selected_twin_fibre_le_class H e w
      _ = t := hUniform w

/-- The selected base occupies at least |V|/t quotient classes. -/
theorem selected_twin_occupied_capacity
    {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph W)
    [Fintype (ClosedTwinQuotient H)]
    [DecidableEq (ClosedTwinQuotient H)]
    (e : V ↪ W) (t : ℕ)
    (hUniform : ∀ w : W, (closedTwinClass H w).card = t) :
    Fintype.card V ≤
      ((Finset.univ : Finset V).image
        (fun v => (Quotient.mk (closedTwinSetoid H) (e v) :
          ClosedTwinQuotient H))).card * t := by
  exact finite_image_fibre_capacity
    (fun v => (Quotient.mk (closedTwinSetoid H) (e v) :
      ClosedTwinQuotient H)) t
    (selected_twin_quotient_fibre_capacity H e t hUniform)

/-- Arithmetic rigidity from uniform class size, occupied-class
capacity, and the positive-degree regular independent-set bound. -/
theorem occupied_quotient_numerical_equalities
    (N M t k : ℕ) (ht : 0 < t)
    (hOrder : M * t = 2 * N)
    (hCapacity : N ≤ k * t)
    (hIndependent : 2 * k ≤ M) :
    N = k * t ∧ M = 2 * k := by
  have hLower : 2 * (k * t) ≤ 2 * N := by
    calc
      2 * (k * t) = (2 * k) * t := by ring
      _ ≤ M * t := Nat.mul_le_mul_right t hIndependent
      _ = 2 * N := hOrder
  have hN : N = k * t := by omega
  have hMul : M * t = (2 * k) * t := by
    calc
      M * t = 2 * N := hOrder
      _ = 2 * (k * t) := by rw [hN]
      _ = (2 * k) * t := by ring
  have hM : M ≤ 2 * k :=
    Nat.le_of_mul_le_mul_right (le_of_eq hMul) ht
  exact ⟨hN, Nat.le_antisymm hM hIndependent⟩

end EPPAIII.TwoGraphs
