import EPPAIII.TwoGraphs.FourWayInternalEquivalence
import EPPAIII.TwoGraphs.TrivialTwoGraphBoth

/-!
# The unrestricted Section 5 all-transversals EPPA equivalence

The manuscript states the equivalence between homogeneity of a finite
two-graph and EPPA for *every* switching representative without an
order restriction. The 3-point nonhomogeneous-switching witness from
the four-way theorem works when |V| >= 3; for |V| <= 2 the two-graph
is trivially homogeneous. Both cases are handled here, so no
unwarranted |V|>=3 hypothesis is imposed on the source-facing result.

The equivalence concerns the actual canonical Taylor double and the
fixed induced transversal embeddings. No outside classification input,
Gardiner, or coherent choice of EPPA lifts is needed.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- Exact source theorem `theo:eppahomtwograph` at *all* finite orders,
including zero, one and two vertices. -/
theorem all_taylor_transversals_eppa_iff_homogeneous_two_graph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∀ t : V → Bool,
      EPPAIII.IsEPPAEmbedding
        (taylorTransversalGraph G t) (taylorPairGraph G)
        (taylorTransversalEmbedding t)) ↔
      IsHomogeneousTwoGraph G := by
  classical
  constructor
  · intro hAll
    by_cases hThree : ∃ x y z : V,
      x ≠ y ∧ x ≠ z ∧ y ≠ z
    · obtain ⟨x,y,z,hxy,hxz,hyz⟩ := hThree
      obtain ⟨t,hNonhom⟩ :=
        switching_class_has_nonhomogeneous_representative
          G x y z hxy hxz hyz
      exact (taylor_fourway_internal_equivalence
        G x y z hxy hxz hyz).mp ⟨t,hNonhom,hAll t⟩ |>.2
    · have hNoEven : ¬ ∃ a b c : V,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ EvenTriple G a b c := by
        rintro ⟨a,b,c,hab,hac,hbc,_⟩
        exact hThree ⟨a,b,c,hab,hac,hbc⟩
      exact no_even_triple_two_graph_homogeneous G hNoEven
  · intro hHom
    exact homogeneous_two_graph_all_transversals_eppa G hHom

/-- A formally transparent four-way conclusion relative to *any*
external classification of homogeneous two-graphs. The classification
is an explicit equivalence, not a Lean axiom. -/
theorem taylor_fourway_relative_to_external_models
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ModelCases : Prop)
    (hClassification : IsHomogeneousTwoGraph G ↔ ModelCases)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∃ t : V → Bool,
      ¬ IsHomogeneousGraph (taylorTransversalGraph G t) ∧
      EPPAIII.IsEPPAEmbedding
        (taylorTransversalGraph G t) (taylorPairGraph G)
        (taylorTransversalEmbedding t)) ↔
    ((∀ t : V → Bool,
      EPPAIII.IsEPPAEmbedding
        (taylorTransversalGraph G t) (taylorPairGraph G)
        (taylorTransversalEmbedding t)) ∧ ModelCases) := by
  constructor
  · intro h
    obtain ⟨hAll,hHom⟩ :=
      (taylor_fourway_internal_equivalence
        G x y z hxy hxz hyz).mp h
    exact ⟨hAll,hClassification.mp hHom⟩
  · rintro ⟨hAll,hModels⟩
    exact (taylor_fourway_internal_equivalence
      G x y z hxy hxz hyz).mpr
        ⟨hAll,hClassification.mpr hModels⟩

end EPPAIII.TwoGraphs
