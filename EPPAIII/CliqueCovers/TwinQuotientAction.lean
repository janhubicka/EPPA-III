import EPPAIII.CliqueCovers.TwinQuotientGraph
import EPPAIII.CliqueCovers.TwinClassTransport

/-!
# Automorphisms descend to the canonical true-twin quotient

Every graph automorphism preserves equality of closed neighbourhoods,
so its vertex permutation descends to a permutation of twin classes.
This descended permutation is an automorphism of the canonical quotient
graph. Consequently vertex-transitivity of H implies vertex-transitivity
of its true-twin quotient.

This completes the group-action input to the positive-degree quotient
independence bound in the zero-partial-profile proof of Lemma 3.7.
No arbitrary representatives or coherent EPPA lifts are chosen.
-/

namespace EPPAIII.CliqueCovers

/-- Equality of closed neighbourhoods is carried both ways by
every graph automorphism. -/
theorem sameClosedNeighbourhood_aut_iff {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) (u v : W) :
    SameClosedNeighbourhood H (q u) (q v) ↔
      SameClosedNeighbourhood H u v := by
  constructor
  · intro h
    have hInv :=
      sameClosedNeighbourhood_automorphism H q.symm
        (graphAutomorphism_symm H q hq) (q u) (q v) h
    simpa using hInv
  · exact sameClosedNeighbourhood_automorphism H q hq u v

/-- An automorphism descends to a permutation of the quotient type. -/
noncomputable def liftTwinAutomorphism {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) :
    Equiv.Perm (ClosedTwinQuotient H) where
  toFun := fun z =>
    Quotient.liftOn z (fun u => Quotient.mk (closedTwinSetoid H) (q u))
      (by
        intro u v huv
        exact Quotient.sound
          (sameClosedNeighbourhood_automorphism H q hq u v huv))
  invFun := fun z =>
    Quotient.liftOn z (fun u => Quotient.mk (closedTwinSetoid H) (q.symm u))
      (by
        intro u v huv
        exact Quotient.sound
          (sameClosedNeighbourhood_automorphism H q.symm
            (graphAutomorphism_symm H q hq) u v huv))
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | _ u =>
      change Quotient.mk (closedTwinSetoid H) (q.symm (q u)) =
        Quotient.mk (closedTwinSetoid H) u
      simp
  right_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | _ u =>
      change Quotient.mk (closedTwinSetoid H) (q (q.symm u)) =
        Quotient.mk (closedTwinSetoid H) u
      simp

/-- Explicit action of a descended automorphism on a class. -/
theorem liftTwinAutomorphism_mk {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) (u : W) :
    liftTwinAutomorphism H q hq (Quotient.mk (closedTwinSetoid H) u) =
      Quotient.mk (closedTwinSetoid H) (q u) :=
  rfl

/-- Every descended automorphism preserves quotient adjacency. -/
theorem liftTwinAutomorphism_graphAut {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) :
    EPPAIII.IsGraphAutomorphism (closedTwinQuotientGraph H)
      (liftTwinAutomorphism H q hq) := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ u =>
    induction y using Quotient.inductionOn with
    | _ v =>
      change
        (¬ SameClosedNeighbourhood H u v ∧ H.Adj u v) ↔
          (¬ SameClosedNeighbourhood H (q u) (q v) ∧
            H.Adj (q u) (q v))
      have hSame := sameClosedNeighbourhood_aut_iff H q hq u v
      constructor
      · rintro ⟨hDifferent,hAdj⟩
        exact ⟨fun h => hDifferent (hSame.mp h),
          (hq u v).mp hAdj⟩
      · rintro ⟨hDifferent,hAdj⟩
        exact ⟨fun h => hDifferent (hSame.mpr h),
          (hq u v).mpr hAdj⟩

/-- A vertex-transitive host has a vertex-transitive
closed-neighbourhood quotient. -/
theorem closedTwinQuotient_transitive {W : Type*}
    (H : SimpleGraph W)
    (hTransitive : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧ q u = v) :
    ∀ x y : ClosedTwinQuotient H,
      ∃ f : Equiv.Perm (ClosedTwinQuotient H),
        EPPAIII.IsGraphAutomorphism (closedTwinQuotientGraph H) f ∧
        f x = y := by
  intro x y
  induction x using Quotient.inductionOn with
  | _ u =>
    induction y using Quotient.inductionOn with
    | _ v =>
      obtain ⟨q,hq,huv⟩ := hTransitive u v
      refine ⟨liftTwinAutomorphism H q hq,
        liftTwinAutomorphism_graphAut H q hq, ?_⟩
      change Quotient.mk (closedTwinSetoid H) (q u) =
        Quotient.mk (closedTwinSetoid H) v
      rw [huv]

end EPPAIII.CliqueCovers
