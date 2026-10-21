import EPPAIII.TwoGraphs.PartialSwitchCompatibleConstant

/-!
# The full partial two-graph switching lemma

Every finite partial automorphism of the odd-edge-parity
two-graph is a partial graph automorphism of some switching
representative of the same graph. The switching representative
is an explicit induced transversal of the canonical Taylor
double, not an assumed invariant graph.

The proof combines independently verified modules:
* anchored XOR discrepancy potential from preservation of triples;
* a single global cycle bit compatible with all even and odd
  cycles, including repeated closed traversals;
* the source-or-removable-cycle property of a finite partial
  permutation;
* strong induction solving all Boolean vertex equations;
* and the final switching adjacency identity.

No automorphism-extension property, external classification,
or additional graph-theoretic hypothesis is assumed.
-/

namespace EPPAIII.TwoGraphs

/-- Full Section 5.1 `lemma:gtg`: every partial automorphism
of the associated two-graph preserves a graph representative
in the original switching class. The domain may be empty,
the partial map may have fixed points, and every finite
combination of open paths and even/odd cycles is included. -/
theorem partial_two_graph_has_switching_representative
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (p : Equiv.Perm V)
    (hp : IsPartialTwoGraphAutomorphism G D p) :
    ∃ t : V → Bool,
      EPPAIII.IsPartialGraphAutomorphism
        (taylorTransversalGraph G t) D p := by
  classical
  obtain ⟨h,hDelta⟩ :=
    partial_two_graph_discrepancy_potential G D p hp
  have hSym : ∀ x y : V,
      decide (G.Adj x y) = decide (G.Adj y x) := by
    intro x y
    by_cases hxy : G.Adj x y
    · have hyx : G.Adj y x := (G.adj_comm x y).mp hxy
      simp [hxy,hyx]
    · have hyx : ¬ G.Adj y x :=
        fun h => hxy ((G.adj_comm x y).mpr h)
      simp [hxy,hyx]
  obtain ⟨c,hCompatible⟩ :=
    exists_globally_compatible_cycle_bit
      (fun x y => decide (G.Adj x y))
      hSym h p D hDelta
  obtain ⟨t,hVertex⟩ :=
    vertex_equations_of_source_or_cycle
      p D h c
      (finite_permutation_has_source_or_removable_cycle p D)
      hCompatible
  exact ⟨t,partial_switch_of_vertex_equations
    G D p h t c hDelta hVertex⟩

end EPPAIII.TwoGraphs
