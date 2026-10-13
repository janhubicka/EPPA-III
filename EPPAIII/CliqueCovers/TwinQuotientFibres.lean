import EPPAIII.CliqueCovers.TwinQuotientCount
import EPPAIII.CliqueCovers.SelectedClassExhaustion
import Mathlib.Data.Fintype.Quotient

/-!
# Exact cardinalities of the fibres of the true-twin quotient

For a vertex-transitive finite graph H the sizes of the fibres of
the canonical closed-neighbourhood quotient map are constant.
If one selected true-twin class has size t, EVERY fibre has t
elements (including the s classes outside a selected sK_t).

The result is expressed as a Fintype.card identity for the subtype
fibre, which allows us to construct an explicit equivalence
Fin t ≃ that fibre using Fintype.equivFinOfCardEq.

This is an interface lemma for constructing the actual outside
twin-fibre labelling in the zero-partial case of Lemma 3.7.
-/

namespace EPPAIII.CliqueCovers

/-- Every quotient fibre has the same cardinality as the
closed-twin class of a specified anchor vertex. -/
theorem closedTwinQuotient_fibre_card_of_transitive {W : Type*}
    [Fintype W]
    (H : SimpleGraph W)
    (hTransitive : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧ q u = v)
    (anchor : W) (z : ClosedTwinQuotient H) :
    Fintype.card
      {w : W // Quotient.mk (closedTwinSetoid H) w = z} =
      (closedTwinClass H anchor).card := by
  classical
  induction z using Quotient.inductionOn with
  | _ v =>
    have hFiber :
        ((Finset.univ : Finset W).filter
          (fun w => Quotient.mk (closedTwinSetoid H) w =
            Quotient.mk (closedTwinSetoid H) v)) =
          closedTwinClass H v :=
      closedTwinQuotient_fiber_mk H v
    calc
      Fintype.card
          {w : W // Quotient.mk (closedTwinSetoid H) w =
            Quotient.mk (closedTwinSetoid H) v} =
        ((Finset.univ : Finset W).filter
          (fun w => Quotient.mk (closedTwinSetoid H) w =
            Quotient.mk (closedTwinSetoid H) v)).card := by
          simp only [Fintype.card_subtype]
      _ = (closedTwinClass H v).card :=
        congrArg Finset.card hFiber
      _ = (closedTwinClass H anchor).card :=
        closedTwinClass_card_of_vertex_transitive
          H hTransitive v anchor

/-- If the selected class of one base vertex has exact size t,
so does every fibre of the quotient, including outside fibres. -/
theorem closedTwinQuotient_fibre_card_eq_t {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (i : Fin s) (a : Fin t)
    (hTransitive : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧ q u = v)
    (hExact : (closedTwinClass H (e (i,a))).card = t)
    (z : ClosedTwinQuotient H) :
    Fintype.card
      {w : W // Quotient.mk (closedTwinSetoid H) w = z} = t := by
  rw [closedTwinQuotient_fibre_card_of_transitive
    H hTransitive (e (i,a)) z, hExact]

/-- Each fibre of the true-twin quotient is consequently
equivalent to Fin t; this uses an explicit cardinality proof
rather than choosing an unverified isomorphism. -/
noncomputable def finEquivClosedTwinFibre {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (i : Fin s) (a : Fin t)
    (hTransitive : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧ q u = v)
    (hExact : (closedTwinClass H (e (i,a))).card = t)
    (z : ClosedTwinQuotient H) :
    Fin t ≃ {w : W // Quotient.mk (closedTwinSetoid H) w = z} :=
  (Fintype.equivFinOfCardEq
    (closedTwinQuotient_fibre_card_eq_t
      H e i a hTransitive hExact z)).symm

end EPPAIII.CliqueCovers
