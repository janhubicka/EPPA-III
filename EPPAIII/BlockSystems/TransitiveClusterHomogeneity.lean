import EPPAIII.TwoGraphs.UniformFibreHomogeneity
import EPPAIII.CliqueCovers.TwinQuotientFibres
import EPPAIII.BlockSystems.ClusterObstructions

/-!
# Finite vertex-transitive cluster graphs are homogeneous

The manuscript's Proposition 6.17 assumes a non-homogeneous
vertex-transitive host, while the independently certified
generalized clique-cover theorems assume a non-cluster host.

This file proves the missing implication, without EPPA or any
classification input. In a cluster graph, the closed-neighbourhood
twin classes are exactly the complete connected components.
Vertex-transitivity gives uniform fibre cardinalities of the
canonical closed-twin quotient. The previously formalized
equal-fibre homogeneity theorem then applies.

The empty graph and singleton graphs are included.
-/

namespace EPPAIII.BlockSystems

open EPPAIII.CliqueCovers
open EPPAIII.TwoGraphs

/-- In a cluster graph two distinct vertices are adjacent exactly
when their closed-neighbourhood quotient classes coincide. -/
theorem cluster_adj_iff_closed_twin_fibre
    {V : Type*}
    (G : SimpleGraph V)
    (hCluster : IsClusterGraph G)
    (x y : V) :
    G.Adj x y ↔
      Quotient.mk (closedTwinSetoid G) x =
        Quotient.mk (closedTwinSetoid G) y ∧ x ≠ y := by
  constructor
  · intro hxy
    have hThird (z : V) (hzx : z ≠ x) (hzy : z ≠ y) :
        G.Adj x z ↔ G.Adj y z := by
      constructor
      · intro hxz
        exact hCluster y x z hxy.symm hxz hzy.symm
      · intro hyz
        exact hCluster x y z hxy hyz hzx.symm
    have hTwin : SameClosedNeighbourhood G x y :=
      closedNeighbourhood_eq_of_true_twins G x y hxy hThird
    exact ⟨Quotient.sound hTwin, G.ne_of_adj hxy⟩
  · rintro ⟨hEq,hxy⟩
    have hTwin : SameClosedNeighbourhood G x y :=
      Quotient.exact hEq
    exact adjacent_of_same_closed_neighbourhood G x y hxy hTwin

/-- A finite vertex-transitive disjoint union of cliques is
homogeneous. The component sizes need not be assumed equal:
they are forced by the actual automorphism action. -/
theorem vertex_transitive_cluster_isHomogeneous
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms G)
    (hCluster : IsClusterGraph G) :
    EPPAIII.DoubleCover.IsHomogeneousGraph G := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨anchor⟩ := hV
    let B := ClosedTwinQuotient G
    letI : Fintype B := Fintype.ofFinite B
    letI : DecidableEq B := Classical.decEq B
    let f : V → B := fun x => Quotient.mk (closedTwinSetoid G) x
    let t : ℕ := (closedTwinClass G anchor).card
    have hCard : ∀ b : B,
        Fintype.card {v : V // f v = b} = t := by
      intro b
      exact closedTwinQuotient_fibre_card_of_transitive
        G hTrans anchor b
    have hAdj (x y : V) :
        G.Adj x y ↔ f x = f y ∧ x ≠ y := by
      exact cluster_adj_iff_closed_twin_fibre G hCluster x y
    exact homogeneous_of_uniform_complete_fibres
      G f t hCard hAdj
  · intro D p _
    refine ⟨Equiv.refl V, ?_, ?_⟩
    · intro x y
      exact (hV ⟨x⟩).elim
    · intro x _
      exact (hV ⟨x⟩).elim

/-- Exact bridge used by Section 6: a vertex-transitive
non-homogeneous finite graph cannot be a cluster graph. -/
theorem transitive_nonhomogeneous_not_cluster
    {V : Type*} [Fintype V]
    (H : SimpleGraph V)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ EPPAIII.DoubleCover.IsHomogeneousGraph H) :
    ¬ IsClusterGraph H := by
  intro hCluster
  exact hNonhomogeneous
    (vertex_transitive_cluster_isHomogeneous H hTrans hCluster)

end EPPAIII.BlockSystems
