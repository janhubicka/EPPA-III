import EPPAIII.CliqueCovers.TwinQuotientAdjacency

/-!
# The canonical simple quotient by closed-neighbourhood twin classes

Closed-neighbourhood equality is an equivalence relation. Distinct
classes have uniform adjacency, allowing a genuinely loopless simple
graph on the quotient type. This quotient is intrinsic to H and makes
no reference to the distinguished EPPA embedding or any arbitrary
choice of representatives.

The key well-definedness argument is supplied by the separately
axiom-audited TwinQuotientAdjacency module.
-/

namespace EPPAIII.CliqueCovers

/-- The canonical equivalence relation of equal closed neighbourhoods. -/
def closedTwinSetoid {W : Type*} (H : SimpleGraph W) : Setoid W where
  r := SameClosedNeighbourhood H
  iseqv := sameClosedNeighbourhood_equivalence H

/-- The vertex type of the canonical true-twin quotient. -/
abbrev ClosedTwinQuotient {W : Type*} (H : SimpleGraph W) :=
  Quotient (closedTwinSetoid H)

/-- Two quotient vertices are adjacent iff their classes differ
and any representatives are adjacent in H. -/
def closedTwinQuotientAdj {W : Type*}
    (H : SimpleGraph W)
    (x y : ClosedTwinQuotient H) : Prop := by
  refine Quotient.liftOn₂ x y
    (fun u v : W => ¬ SameClosedNeighbourhood H u v ∧ H.Adj u v)
    ?_
  intro u v u' v' hu hv
  apply propext
  constructor
  · rintro ⟨hDiff,hAdj⟩
    have hDiff' : ¬ SameClosedNeighbourhood H u' v' := by
      intro hSame
      exact hDiff ((hu.trans hSame).trans hv.symm)
    have hAdj' :=
      (adj_iff_of_distinct_twin_classes H u u' v v' hu hv hDiff).mp hAdj
    exact ⟨hDiff',hAdj'⟩
  · rintro ⟨hDiff',hAdj'⟩
    have hDiff : ¬ SameClosedNeighbourhood H u v := by
      intro hSame
      exact hDiff' ((hu.symm.trans hSame).trans hv)
    exact ⟨hDiff,
      (adj_iff_of_distinct_twin_classes H u u' v v' hu hv hDiff).mpr hAdj'⟩

/-- The canonical quotient is a loopless undirected graph. -/
def closedTwinQuotientGraph {W : Type*}
    (H : SimpleGraph W) : SimpleGraph (ClosedTwinQuotient H) where
  Adj := closedTwinQuotientAdj H
  symm := by
    constructor
    intro x y h
    induction x using Quotient.inductionOn with
    | _ u =>
      induction y using Quotient.inductionOn with
      | _ v =>
        change ¬ SameClosedNeighbourhood H u v ∧ H.Adj u v at h
        change ¬ SameClosedNeighbourhood H v u ∧ H.Adj v u
        exact ⟨fun hvu => h.1 hvu.symm, h.2.symm⟩
  loopless := by
    constructor
    intro x h
    induction x using Quotient.inductionOn with
    | _ u =>
      change ¬ SameClosedNeighbourhood H u u ∧ H.Adj u u at h
      exact h.1 rfl

/-- Concrete adjacency formula on classes represented by vertices. -/
theorem closedTwinQuotient_adj_mk {W : Type*}
    (H : SimpleGraph W) (u v : W) :
    (closedTwinQuotientGraph H).Adj
      (Quotient.mk (closedTwinSetoid H) u)
      (Quotient.mk (closedTwinSetoid H) v) ↔
        ¬ SameClosedNeighbourhood H u v ∧ H.Adj u v := by
  rfl

end EPPAIII.CliqueCovers
