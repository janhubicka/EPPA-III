import EPPAIII.TwoGraphs.OccupiedTwinFibreCount

/-!
# Equality in the selected true-twin occupancy bound

If the finite selected graph saturates the common upper bound
on the size of every occupied true-twin quotient fibre, then
each occupied fibre is completely filled by selected vertices.

This is a generic finite counting lemma independent of EPPA,
vertex-transitivity, Taylor doubles, and graph classification.
The source's first quotient case needs precisely this inference
after the numerical equalities are obtained.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- Equality in the finite image capacity bound forces every
occupied fibre to attain its common size upper bound. -/
theorem finite_image_fibres_full_of_capacity_eq
    {V Q : Type*} [Fintype V] [Fintype Q]
    [DecidableEq V] [DecidableEq Q]
    (f : V → Q) (t : ℕ)
    (hUpper : ∀ q : Q,
      ((Finset.univ : Finset V).filter (fun v => f v = q)).card ≤ t)
    (hEq : Fintype.card V =
      ((Finset.univ : Finset V).image f).card * t)
    (q : Q)
    (hq : q ∈ (Finset.univ : Finset V).image f) :
    ((Finset.univ : Finset V).filter (fun v => f v = q)).card = t := by
  classical
  let I : Finset Q := (Finset.univ : Finset V).image f
  let fibre : Q → Finset V :=
    fun b => (Finset.univ : Finset V).filter (fun v => f v = b)
  have hEmpty (b : Q) (hb : b ∉ I) : (fibre b).card = 0 := by
    by_contra h
    have hPos : 0 < (fibre b).card := Nat.pos_of_ne_zero h
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hPos
    exact hb (Finset.mem_image.mpr
      ⟨v, Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩)
  have hCount : Fintype.card V =
      ∑ b : Q, (fibre b).card := by
    simpa [fibre] using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset V))
        (t := (Finset.univ : Finset Q))
        (f := f) (by intro _ _; simp))
  have hOnly : (∑ b ∈ I, (fibre b).card) =
      ∑ b : Q, (fibre b).card := by
    apply Finset.sum_subset (Finset.subset_univ I)
    intro b _ hb
    exact hEmpty b hb
  have hSum : (∑ b ∈ I, (fibre b).card) =
      ∑ _b ∈ I, t := by
    calc
      (∑ b ∈ I, (fibre b).card) =
          Fintype.card V := hOnly.trans hCount.symm
      _ = I.card * t := by simpa only [I] using hEq
      _ = ∑ _b ∈ I, t := by simp
  have hEach :
      ∀ b ∈ I, (fibre b).card = t := by
    exact (Finset.sum_eq_sum_iff_of_le
      (fun b _ => hUpper b)).mp hSum
  exact hEach q hq

/-- For true-twin classes, equality in the selected occupied
quotient bound means every selected class is saturated. -/
theorem selected_twin_quotient_occupied_class_full
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    (H : SimpleGraph W)
    [Fintype (ClosedTwinQuotient H)]
    [DecidableEq (ClosedTwinQuotient H)]
    (e : V ↪ W) (t : ℕ)
    (hUniform : ∀ w : W, (closedTwinClass H w).card = t)
    (hExact : Fintype.card V =
      ((Finset.univ : Finset V).image
        (fun v => (Quotient.mk (closedTwinSetoid H) (e v) :
          ClosedTwinQuotient H))).card * t)
    (q : ClosedTwinQuotient H)
    (hq : q ∈ ((Finset.univ : Finset V).image
      (fun v => (Quotient.mk (closedTwinSetoid H) (e v) :
        ClosedTwinQuotient H)))) :
    ((Finset.univ : Finset V).filter (fun v =>
      (Quotient.mk (closedTwinSetoid H) (e v) :
        ClosedTwinQuotient H) = q)).card = t := by
  classical
  exact finite_image_fibres_full_of_capacity_eq
    (fun v => (Quotient.mk (closedTwinSetoid H) (e v) :
      ClosedTwinQuotient H)) t
    (selected_twin_quotient_fibre_capacity H e t hUniform)
    hExact q hq

end EPPAIII.TwoGraphs
