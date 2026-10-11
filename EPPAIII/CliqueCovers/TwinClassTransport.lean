import EPPAIII.CliqueCovers.ClosedTwinClasses
import EPPAIII.EPPA.Definitions

/-!
# Automorphisms transport closed-neighbourhood twin classes

Equality of closed neighbourhoods defines the canonical true-twin
equivalence relation. A graph automorphism carries a twin class
bijectively to the twin class of the image vertex. Thus all twin
classes have the same size in a vertex-transitive host.

This is a quotient-independent way to obtain the equal class sizes
used in the zero-partial-profile proof of Lemma 3.7.
-/

namespace EPPAIII.CliqueCovers

/-- The inverse of a graph automorphism is again an automorphism. -/
theorem graphAutomorphism_symm {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) :
    EPPAIII.IsGraphAutomorphism H q.symm := by
  intro u v
  have h := hq (q.symm u) (q.symm v)
  simpa using h.symm

/-- A closed neighbourhood is transported by a graph automorphism. -/
theorem closedNeighbourhood_mem_automorphism {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q)
    (u w : W) :
    w ∈ closedNeighbourhood H (q u) ↔
      q.symm w ∈ closedNeighbourhood H u := by
  change (w = q u ∨ H.Adj (q u) w) ↔
    (q.symm w = u ∨ H.Adj u (q.symm w))
  have hEq : w = q u ↔ q.symm w = u := by
    constructor
    · intro hw
      simp [hw]
    · intro hw
      have h := congrArg q hw
      simpa using h
  have hAdj : H.Adj (q u) w ↔ H.Adj u (q.symm w) := by
    have h := hq u (q.symm w)
    simpa using h.symm
  exact or_congr hEq hAdj

/-- The twin-class relation is preserved by graph automorphisms. -/
theorem sameClosedNeighbourhood_automorphism {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q)
    (u v : W) (hSame : SameClosedNeighbourhood H u v) :
    SameClosedNeighbourhood H (q u) (q v) := by
  unfold SameClosedNeighbourhood at *
  ext w
  calc
    w ∈ closedNeighbourhood H (q u) ↔
      q.symm w ∈ closedNeighbourhood H u :=
      closedNeighbourhood_mem_automorphism H q hq u w
    _ ↔ q.symm w ∈ closedNeighbourhood H v := by rw [hSame]
    _ ↔ w ∈ closedNeighbourhood H (q v) :=
      (closedNeighbourhood_mem_automorphism H q hq v w).symm

/-- The finite canonical twin class of a vertex. -/
noncomputable def closedTwinClass {W : Type*} [Fintype W]
    (H : SimpleGraph W) (u : W) : Finset W := by
  classical
  exact Finset.univ.filter (fun v => SameClosedNeighbourhood H u v)

/-- Graph automorphisms map each canonical twin class exactly onto
the twin class of its image vertex. -/
theorem closedTwinClass_map_automorphism {W : Type*} [Fintype W]
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) (u : W) :
    (closedTwinClass H u).map q.toEmbedding =
      closedTwinClass H (q u) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨v,hv,hqv⟩ := Finset.mem_map.mp hw
    have hvSame : SameClosedNeighbourhood H u v := by
      exact (Finset.mem_filter.mp hv).2
    have hSame := sameClosedNeighbourhood_automorphism H q hq u v hvSame
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [← hqv] using hSame
  · intro hw
    have hSame : SameClosedNeighbourhood H (q u) w :=
      (Finset.mem_filter.mp hw).2
    have hInv := sameClosedNeighbourhood_automorphism
      H q.symm (graphAutomorphism_symm H q hq) (q u) w hSame
    refine Finset.mem_map.mpr ⟨q.symm w, ?_, by simp⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa using hInv⟩

/-- Graph automorphisms preserve twin-class cardinalities. -/
theorem closedTwinClass_card_automorphism {W : Type*} [Fintype W]
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) (u : W) :
    (closedTwinClass H (q u)).card = (closedTwinClass H u).card := by
  classical
  rw [← closedTwinClass_map_automorphism H q hq u]
  exact Finset.card_map _

/-- Actual vertex-transitivity makes all true-twin classes
equinumerous. No quotient graph is needed for this statement. -/
theorem closedTwinClass_card_of_vertex_transitive
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (hTransitive : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧ q u = v)
    (u v : W) :
    (closedTwinClass H u).card = (closedTwinClass H v).card := by
  obtain ⟨q,hq,hqu⟩ := hTransitive u v
  simpa [hqu] using (closedTwinClass_card_automorphism H q hq u).symm

end EPPAIII.CliqueCovers
