import EPPAIII.TwoGraphs.SwitchingClassNonhomogeneous
import EPPAIII.TwoGraphs.AllTransversalEppa
import EPPAIII.BlockSystems.GraphTransport

/-!
# The elementary three directions of the four-way two-graph theorem

The source's four-way theorem has an *external* classification of
homogeneous two-graphs as its fourth direction. Here we finish the
three internal EPPA/homogeneity directions under |X| >= 3.

The key missing interface is the actual host equivalence which
identifies the Taylor double of a switched representative with
the original Taylor double. It maps its canonical bottom half to
the chosen switching transversal.

The proof then applies the already verified one-for-all theorem
to the non-homogeneous representative and transports its two-graph
homogeneity back along the equality of triple parities. No choice
of group actions, hidden equivalence of hosts, or external
classification is assumed.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover
open EPPAIII.BlockSystems

/-- A fibrewise Boolean flip; it is its own inverse. -/
def switchingFibreEquiv {V : Type*} (t : V → Bool) :
    Bool × V ≃ Bool × V where
  toFun := fun u => (Bool.xor u.1 (t u.2),u.2)
  invFun := fun u => (Bool.xor u.1 (t u.2),u.2)
  left_inv := by
    intro u
    rcases u with ⟨b,x⟩
    cases b <;> cases ht : t x <;> simp [ht, Bool.xor]
  right_inv := by
    intro u
    rcases u with ⟨b,x⟩
    cases b <;> cases ht : t x <;> simp [ht, Bool.xor]

/-- The bottom half of the switched Taylor graph maps precisely
to the chosen transversal of the original Taylor graph. -/
theorem switchingFibreEquiv_bottom {V : Type*}
    (t : V → Bool) (x : V) :
    switchingFibreEquiv t (false,x) =
      taylorTransversalEmbedding t x := by
  change (Bool.xor false (t x),x) = (t x,x)
  cases ht : t x <;> simp [ht, Bool.xor]

/-- An exact graph equality after pulling back the original host.
In particular the inverse switching map preserves all host adjacency,
including absence of mate edges. -/
theorem switchingFibreEquiv_taylor_pullback
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : V → Bool) :
    pullbackGraph (taylorPairGraph G) (switchingFibreEquiv t) =
      taylorPairGraph (taylorTransversalGraph G t) := by
  classical
  apply SimpleGraph.ext
  funext u v
  apply propext
  rcases u with ⟨b,x⟩
  rcases v with ⟨c,y⟩
  change
    (x ≠ y ∧
      (G.Adj x y ↔
        Bool.xor b (t x) = Bool.xor c (t y))) ↔
    (x ≠ y ∧
      ((x ≠ y ∧ (G.Adj x y ↔ t x = t y)) ↔ b = c))
  by_cases hxy : x = y
  · subst y
    simp
  · cases b <;> cases c <;>
      cases htX : t x <;> cases htY : t y <;>
      by_cases hG : G.Adj x y <;>
      simp_all [Bool.xor]

/-- Any non-homogeneous EPPA transversal of a Taylor double
forces the *original* two-graph to be homogeneous, even if that
transversal is not the originally selected bottom copy. -/
theorem nonhomogeneous_transversal_eppa_implies_two_graph_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : V → Bool)
    (hNonhomogeneous :
      ¬ IsHomogeneousGraph (taylorTransversalGraph G t))
    (heppa :
      EPPAIII.IsEPPAEmbedding
        (taylorTransversalGraph G t) (taylorPairGraph G)
        (taylorTransversalEmbedding t)) :
    IsHomogeneousTwoGraph G := by
  classical
  let J := taylorTransversalGraph G t
  letI : DecidableRel J.Adj := by infer_instance
  have hPull :
      EPPAIII.IsEPPAEmbedding J
        (pullbackGraph (taylorPairGraph G) (switchingFibreEquiv t))
        (bottomEmbedding V) :=
    eppa_pullback_bottom J (taylorPairGraph G)
      (taylorTransversalEmbedding t) heppa
      (switchingFibreEquiv t)
      (switchingFibreEquiv_bottom t)
  have hEPPAJ :
      EPPAIII.IsEPPAEmbedding J (taylorPairGraph J)
        (bottomEmbedding V) := by
    rw [← switchingFibreEquiv_taylor_pullback G t]
    exact hPull
  letI : Fintype (EPPAIII.CliqueCovers.ClosedTwinQuotient
      (taylorPairGraph J)) := Fintype.ofFinite _
  letI : DecidableEq (EPPAIII.CliqueCovers.ClosedTwinQuotient
      (taylorPairGraph J)) := Classical.decEq _
  letI : DecidableRel
      (EPPAIII.CliqueCovers.closedTwinQuotientGraph
        (taylorPairGraph J)).Adj := by infer_instance
  have hHomJ : IsHomogeneousTwoGraph J :=
    taylor_eppa_two_graph_homogeneous_all_cases
      J hEPPAJ hNonhomogeneous
  have hParity (x y z : V) :
      OddBaseTriple J x y z ↔ OddBaseTriple G x y z :=
    odd_triple_transversal_iff G t x y z
  intro D p hp
  have hpJ : IsPartialTwoGraphAutomorphism J D p := by
    intro x hx y hy z hz
    exact (hParity x y z).trans
      ((hp x hx y hy z hz).trans (hParity (p x) (p y) (p z)).symm)
  obtain ⟨σ,hσ,hExtend⟩ := hHomJ D p hpJ
  refine ⟨σ, ?_, hExtend⟩
  intro x y z
  exact (hParity x y z).symm.trans
    ((hσ x y z).trans (hParity (σ x) (σ y) (σ z)))

/-- The three internal statements in the four-way theorem are
equivalent; Gardiner's separate classification of homogeneous
two-graphs is the only external implication. -/
theorem taylor_fourway_internal_equivalence
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∃ t : V → Bool,
      ¬ IsHomogeneousGraph (taylorTransversalGraph G t) ∧
      EPPAIII.IsEPPAEmbedding
        (taylorTransversalGraph G t) (taylorPairGraph G)
        (taylorTransversalEmbedding t)) ↔
    (∀ t : V → Bool,
      EPPAIII.IsEPPAEmbedding
        (taylorTransversalGraph G t) (taylorPairGraph G)
        (taylorTransversalEmbedding t)) ∧
    IsHomogeneousTwoGraph G := by
  constructor
  · rintro ⟨t,hNonhom,hEPPA⟩
    have hHom : IsHomogeneousTwoGraph G :=
      nonhomogeneous_transversal_eppa_implies_two_graph_homogeneous
        G t hNonhom hEPPA
    exact ⟨homogeneous_two_graph_all_transversals_eppa G hHom,hHom⟩
  · intro h
    obtain ⟨t,hNonhom⟩ :=
      switching_class_has_nonhomogeneous_representative
        G x y z hxy hxz hyz
    exact ⟨t,hNonhom,h.1 t⟩

end EPPAIII.TwoGraphs
