import EPPAIII.TwoGraphs.ComplementaryOnePoint

/-!
# One-for-all: homogeneous two-graph from one EPPA transversal

The main combinatorial argument is a finite-set induction. After
extending the restriction of a partial two-graph automorphism to R,
its last point becomes a one-point map a -> b fixing R. Equality
of triple parities is inherited through the already constructed
two-graph automorphism. The complementary and equal graph types
were discharged in ComplementaryOnePoint.lean.

The theorem quantifies over actual partial permutations and
produces actual total automorphisms of the odd-parity two-graph.
No nonstandard axiom or graph classification is used.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- A partial automorphism of the odd-edge-parity two-graph,
represented as the restriction of a permutation to a finite domain. -/
def IsPartialTwoGraphAutomorphism
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (p : Equiv.Perm V) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
    OddBaseTriple G x y z ↔
      OddBaseTriple G (p x) (p y) (p z)

/-- Homogeneity of the associated finite two-graph. -/
def IsHomogeneousTwoGraph
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (D : Finset V) (p : Equiv.Perm V),
    IsPartialTwoGraphAutomorphism G D p →
      ∃ σ : Equiv.Perm V,
        IsTwoGraphAutomorphism G σ ∧
        (∀ x ∈ D, σ x = p x)

/-- Any one-point extension property for the two-graph suffices to
extend all of its finite partial automorphisms. -/
theorem two_graph_homogeneous_of_one_point_extensions
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hOne : ∀ (R : Finset V) (a b : V),
      a ≠ b → a ∉ R → b ∉ R →
      (∀ r ∈ R, ∀ s ∈ R,
        OddBaseTriple G a r s ↔ OddBaseTriple G b r s) →
      ∃ τ : Equiv.Perm V,
        IsTwoGraphAutomorphism G τ ∧ τ a = b ∧
        (∀ r ∈ R, τ r = r)) :
    IsHomogeneousTwoGraph G := by
  classical
  intro D
  induction D using Finset.induction with
  | empty =>
      intro p hPartial
      refine ⟨Equiv.refl V,?_,?_⟩
      · intro x y z
        rfl
      · intro x hx
        simp at hx
  | @insert a R ha ih =>
      intro p hPartial
      have hRestriction : IsPartialTwoGraphAutomorphism G R p := by
        intro x hx y hy z hz
        exact hPartial x (Finset.mem_insert_of_mem hx)
          y (Finset.mem_insert_of_mem hy)
          z (Finset.mem_insert_of_mem hz)
      obtain ⟨σ,hσ,hσR⟩ := ih p hRestriction
      let b : V := σ.symm (p a)
      have hσb : σ b = p a := by simp [b]
      by_cases heq : b = a
      · refine ⟨σ,hσ,?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with hza | hzR
        · subst z
          calc
            σ a = σ b := by simp [heq]
            _ = p a := hσb
        · exact hσR z hzR
      · have hab : a ≠ b := Ne.symm heq
        have hbR : b ∉ R := by
          intro hbR
          have hpa : p a = p b :=
            hσb.symm.trans (hσR b hbR)
          exact heq (p.injective hpa).symm
        have hParity : ∀ r ∈ R, ∀ s ∈ R,
            OddBaseTriple G a r s ↔ OddBaseTriple G b r s := by
          intro r hr s hs
          have hP := hPartial a (Finset.mem_insert_self a R)
            r (Finset.mem_insert_of_mem hr)
            s (Finset.mem_insert_of_mem hs)
          have hI := hσ b r s
          rw [hσb, hσR r hr, hσR s hs] at hI
          exact hP.trans hI.symm
        obtain ⟨τ,hτ,hτa,hτR⟩ :=
          hOne R a b hab ha hbR hParity
        let ρ : Equiv.Perm V := τ.trans σ
        have hρ : IsTwoGraphAutomorphism G ρ := by
          intro x y z
          exact (hτ x y z).trans
            (hσ (τ x) (τ y) (τ z))
        refine ⟨ρ,hρ,?_⟩
        intro z hz
        rcases Finset.mem_insert.mp hz with hza | hzR
        · subst z
          change σ (τ a) = p a
          rw [hτa]
          exact hσb
        · change σ (τ z) = p z
          rw [hτR z hzR]
          exact hσR z hzR

/-- Full one-for-all conclusion conditional on an actual invariant
Taylor fibre system, EPPA for the bottom transversal and
non-homogeneity of G. -/
theorem taylor_eppa_two_graph_homogeneous_of_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heppa : EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G) :
    IsHomogeneousTwoGraph G := by
  apply two_graph_homogeneous_of_one_point_extensions G
  intro R a b hab ha hb hParity
  exact eppa_one_point_two_graph_extension_of_pairs
    G heppa hPairs hNonhomogeneous R a b hab ha hb hParity

/-- Source-facing nontrivial Section 5 one-for-all theorem. The
invariant two-point fibre system is derived from the true-twin
quotient argument, not an extra assumption. -/
theorem taylor_eppa_two_graph_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (EPPAIII.CliqueCovers.ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (EPPAIII.CliqueCovers.ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (EPPAIII.CliqueCovers.closedTwinQuotientGraph
      (taylorPairGraph G)).Adj]
    (heppa : EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G)
    (hEven : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      EvenTriple G a b c) :
    IsHomogeneousTwoGraph G := by
  exact taylor_eppa_two_graph_homogeneous_of_pairs
    G heppa
    (taylor_eppa_intrinsic_fibres G heppa hNonhomogeneous hEven)
    hNonhomogeneous

end EPPAIII.TwoGraphs
