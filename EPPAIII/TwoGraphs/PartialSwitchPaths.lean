import EPPAIII.TwoGraphs.PartialSwitchCoboundary

/-!
# Partial switching on open directed paths

A finite partial injection with no directed cycle has an
elimination order in which each nonempty remaining subset
contains a vertex with no incoming arrow from that subset.

For *any* Boolean equation labels h and global bit c, the system
  t(x) XOR t(p(x)) = h(x) XOR c  (x in D)
can be solved by recursively eliminating such a source x.
After solving the smaller subsystem, assign t(x) to satisfy its
own equation. No previously solved equation depends on t(x)
because there is no remaining arrow into x.

The source-property assumption is stated explicitly; proving its
equivalence with a purely dynamical no-cycle condition is separate.
This already handles arbitrary disjoint unions of directed paths.
-/

namespace EPPAIII.TwoGraphs

/-- Every nonempty subset of D has a vertex without any
incoming p-edge from that subset. This is the acyclicity
property needed for finite source elimination. -/
def HasPartialSources {V : Type*} (p : Equiv.Perm V)
    (D : Finset V) : Prop :=
  ∀ E : Finset V, E ⊆ D → E.Nonempty →
    ∃ x ∈ E, ∀ y ∈ E, p y ≠ x

/-- Solve arbitrary prescribed Boolean labels on each partial
permutation arrow, provided there are no directed cycles.
The proof chooses a source in each remaining finite subsystem. -/
theorem vertex_equations_of_partial_sources
    {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (D : Finset V)
    (h : V → Bool) (c : Bool)
    (hSources : HasPartialSources p D) :
    ∃ t : V → Bool,
      ∀ x ∈ D,
        Bool.xor (t x) (t (p x)) = Bool.xor (h x) c := by
  classical
  have aux : ∀ E : Finset V, E ⊆ D →
      ∃ t : V → Bool,
        ∀ x ∈ E,
          Bool.xor (t x) (t (p x)) = Bool.xor (h x) c := by
    intro E
    refine Finset.strongInductionOn E ?_
    intro S ih hSD
    by_cases hS : S.Nonempty
    · obtain ⟨x,hx,hNoIncoming⟩ := hSources S hSD hS
      have hSmall : S.erase x ⊆ D :=
        (Finset.erase_subset x S).trans hSD
      obtain ⟨t,ht⟩ :=
        ih (S.erase x) (Finset.erase_ssubset hx) hSmall
      let tx : Bool := Bool.xor (Bool.xor (h x) c) (t (p x))
      let T : V → Bool := fun z => if z = x then tx else t z
      refine ⟨T, ?_⟩
      intro y hy
      by_cases hyx : y = x
      · subst y
        have hpx : p x ≠ x := hNoIncoming x hx
        change Bool.xor
          (if x = x then tx else t x)
          (if p x = x then tx else t (p x)) =
            Bool.xor (h x) c
        simp only [if_pos rfl, if_neg hpx]
        dsimp [tx]
        cases hh : h x <;>
          cases hc : c <;>
          cases htpx : t (p x) <;> decide
      · have hySmall : y ∈ S.erase x :=
          Finset.mem_erase.mpr ⟨hyx,hy⟩
        have hpy : p y ≠ x := hNoIncoming y hy
        have hOld := ht y hySmall
        change Bool.xor
          (if y = x then tx else t y)
          (if p y = x then tx else t (p y)) =
            Bool.xor (h y) c
        simpa only [if_neg hyx, if_neg hpy] using hOld
    · refine ⟨fun _ => false, ?_⟩
      intro x hx
      exact (hS ⟨x,hx⟩).elim
  exact aux D (Finset.Subset.rfl)

/-- Any partial two-graph automorphism with the source-elimination
property preserves some switching representative. This uses the
actual potential from triple parity, not a free discrepancy axiom. -/
theorem partial_two_graph_acyclic_switch
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (p : Equiv.Perm V)
    (hp : IsPartialTwoGraphAutomorphism G D p)
    (hSources : HasPartialSources p D) :
    ∃ t : V → Bool,
      EPPAIII.IsPartialGraphAutomorphism
        (taylorTransversalGraph G t) D p := by
  obtain ⟨h,hDelta⟩ :=
    partial_two_graph_discrepancy_potential G D p hp
  obtain ⟨t,ht⟩ :=
    vertex_equations_of_partial_sources p D h false hSources
  exact ⟨t,partial_switch_of_vertex_equations
    G D p h t false hDelta ht⟩

end EPPAIII.TwoGraphs
