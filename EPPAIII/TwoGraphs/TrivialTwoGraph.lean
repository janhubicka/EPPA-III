import EPPAIII.TwoGraphs.OneForAll

/-!
# The trivial two-graph case of Proposition 5.11

If no triple of pairwise distinct vertices has even edge parity,
the associated two-graph contains *every* distinct triple. Every
permutation is then an automorphism, so it is homogeneous without
any EPPA or fibre-rigidity hypothesis.

This closes the exception handled separately at the beginning of
the printed Proposition 5.11. For the remaining case we use the
now-verified finite-set induction plus EPPA fibre rigidity.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- The graph-theoretic even-triple predicate is precisely
negation of the Boolean odd-parity predicate, for all triples
including repeated vertices. -/
theorem even_triple_iff_not_odd
    {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V) :
    EvenTriple G x y z ↔ ¬ OddBaseTriple G x y z := by
  have hzx : decide (G.Adj z x) = decide (G.Adj x z) := by
    by_cases h : G.Adj x z
    · have hz : G.Adj z x := (G.adj_comm x z).mp h
      simp [h,hz]
    · have hz : ¬ G.Adj z x :=
        fun hv => h ((G.adj_comm x z).mpr hv)
      simp [h,hz]
  unfold OddBaseTriple
  rw [hzx]
  by_cases hab : G.Adj x y <;>
    by_cases hbc : G.Adj y z <;>
    by_cases hac : G.Adj x z <;>
    simp_all [EvenTriple, Bool.xor]

/-- In a graph with no even-parity triple on three distinct base
vertices, EVERY permutation preserves the associated two-graph. -/
theorem no_even_triple_all_two_graph_automorphisms
    {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNoEven : ¬ ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ EvenTriple G a b c)
    (σ : Equiv.Perm V) :
    IsTwoGraphAutomorphism G σ := by
  intro x y z
  by_cases hxy : x = y
  · subst y
    have hA := oddBaseTriple_repeated_false G x x z (Or.inl rfl)
    have hB := oddBaseTriple_repeated_false G
      (σ x) (σ x) (σ z) (Or.inl rfl)
    exact ⟨fun hh => (hA hh).elim, fun hh => (hB hh).elim⟩
  by_cases hyz : y = z
  · subst z
    have hA := oddBaseTriple_repeated_false G x y y
      (Or.inr (Or.inl rfl))
    have hB := oddBaseTriple_repeated_false G
      (σ x) (σ y) (σ y) (Or.inr (Or.inl rfl))
    exact ⟨fun hh => (hA hh).elim, fun hh => (hB hh).elim⟩
  by_cases hzx : z = x
  · subst z
    have hA := oddBaseTriple_repeated_false G x y x
      (Or.inr (Or.inr rfl))
    have hB := oddBaseTriple_repeated_false G
      (σ x) (σ y) (σ x) (Or.inr (Or.inr rfl))
    exact ⟨fun hh => (hA hh).elim, fun hh => (hB hh).elim⟩
  have hxz : x ≠ z := Ne.symm hzx
  have hOdd : ∀ a b c : V, a ≠ b → a ≠ c → b ≠ c →
      OddBaseTriple G a b c := by
    intro a b c hab hac hbc
    by_contra hn
    apply hNoEven
    exact ⟨a,b,c,hab,hac,hbc,
      (even_triple_iff_not_odd G a b c).mpr hn⟩
  have hA := hOdd x y z hxy hxz hyz
  have hB := hOdd (σ x) (σ y) (σ z)
    (σ.injective.ne hxy) (σ.injective.ne hxz)
    (σ.injective.ne hyz)
  exact ⟨fun _ => hB,fun _ => hA⟩

/-- The complete two-graph, including orders 0,1,2, is homogeneous:
extend each partial permutation by that same global permutation. -/
theorem no_even_triple_two_graph_homogeneous
    {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNoEven : ¬ ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ EvenTriple G a b c) :
    IsHomogeneousTwoGraph G := by
  intro D p _
  exact ⟨p,no_even_triple_all_two_graph_automorphisms G hNoEven p,
    fun _ _ => rfl⟩

/-- Unconditional homogeneity conclusion of Proposition 5.11:
the trivial two-graph case requires no fibre rigidity, while
the nontrivial case invokes the verified genuine EPPA induction. -/
theorem taylor_eppa_two_graph_homogeneous_all_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (EPPAIII.CliqueCovers.ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (EPPAIII.CliqueCovers.ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (EPPAIII.CliqueCovers.closedTwinQuotientGraph
      (taylorPairGraph G)).Adj]
    (heppa : EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G) :
    IsHomogeneousTwoGraph G := by
  by_cases hEven : ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ EvenTriple G a b c
  · exact taylor_eppa_two_graph_homogeneous
      G heppa hNonhomogeneous hEven
  · exact no_even_triple_two_graph_homogeneous G hEven

end EPPAIII.TwoGraphs
