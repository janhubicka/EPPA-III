import EPPAIII.CliqueCovers.TwinQuotientAction
import EPPAIII.CliqueCovers.TwinClassTransport
import Mathlib.Data.Fintype.Quotient

/-!
# Cardinality of the canonical true-twin quotient

The quotient map partitions all host vertices into disjoint fibers,
each exactly a closed-neighbourhood twin class. When every class has
the same finite size a, double-counting the quotient fibers gives

  |W| = |W / (same closed neighbourhood)| * a.

In a vertex-transitive host the uniform-size assumption follows from
the previously verified automorphism transport of twin classes.
Combined with the lower bound a ≥ t for selected cliques, this
yields |Q| ≤ 2s in a host of size 2st.
-/

namespace EPPAIII.CliqueCovers

/-- The quotient fiber over the class of v is precisely
the finite closed-neighbourhood class of v. -/
theorem closedTwinQuotient_fiber_mk {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableEq (ClosedTwinQuotient H)] (v : W) :
    ((Finset.univ : Finset W).filter
      (fun w => Quotient.mk (closedTwinSetoid H) w =
        Quotient.mk (closedTwinSetoid H) v)) =
      closedTwinClass H v := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hw
    have hSame : SameClosedNeighbourhood H w v := Quotient.exact hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSame.symm⟩
  · intro hw
    have hSame : SameClosedNeighbourhood H v w :=
      (Finset.mem_filter.mp hw).2
    exact Quotient.sound hSame.symm

/-- If all twin classes have the same size as the class of u,
the quotient cardinality times that class size equals |W|. -/
theorem closedTwinQuotient_card_mul_class_card {W : Type*}
    [Fintype W]
    (H : SimpleGraph W)
    [Fintype (ClosedTwinQuotient H)]
    (u : W)
    (hUniform : ∀ v : W,
      (closedTwinClass H v).card = (closedTwinClass H u).card) :
    Fintype.card (ClosedTwinQuotient H) *
      (closedTwinClass H u).card = Fintype.card W := by
  classical
  let π : W → ClosedTwinQuotient H :=
    fun w => Quotient.mk (closedTwinSetoid H) w
  have hFiber (z : ClosedTwinQuotient H) :
      ((Finset.univ : Finset W).filter (fun w => π w = z)).card =
        (closedTwinClass H u).card := by
    induction z using Quotient.inductionOn with
    | _ v =>
      change ((Finset.univ : Finset W).filter
        (fun w => Quotient.mk (closedTwinSetoid H) w =
          Quotient.mk (closedTwinSetoid H) v)).card =
            (closedTwinClass H u).card
      rw [closedTwinQuotient_fiber_mk H v]
      exact hUniform v
  have hCount :
      Fintype.card W =
        ∑ z : ClosedTwinQuotient H,
          ((Finset.univ : Finset W).filter (fun w => π w = z)).card := by
    simpa using
      (Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset W))
        (t := (Finset.univ : Finset (ClosedTwinQuotient H)))
        (f := π) (by intro _ _; simp))
  calc
    Fintype.card (ClosedTwinQuotient H) *
        (closedTwinClass H u).card =
      ∑ z : ClosedTwinQuotient H, (closedTwinClass H u).card := by simp
    _ = ∑ z : ClosedTwinQuotient H,
          ((Finset.univ : Finset W).filter (fun w => π w = z)).card := by
            apply Finset.sum_congr rfl
            intro z _
            exact (hFiber z).symm
    _ = Fintype.card W := hCount.symm

/-- In a vertex-transitive host all twin classes have the same size,
so the quotient-fiber cardinality identity holds automatically. -/
theorem closedTwinQuotient_card_mul_class_of_transitive {W : Type*}
    [Fintype W]
    (H : SimpleGraph W)
    [Fintype (ClosedTwinQuotient H)]
    (hTransitive : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧ q u = v)
    (u : W) :
    Fintype.card (ClosedTwinQuotient H) *
      (closedTwinClass H u).card = Fintype.card W := by
  apply closedTwinQuotient_card_mul_class_card H u
  intro v
  exact closedTwinClass_card_of_vertex_transitive H hTransitive v u

end EPPAIII.CliqueCovers
