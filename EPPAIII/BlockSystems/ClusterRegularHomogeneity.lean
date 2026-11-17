import EPPAIII.BlockSystems.TransitiveClusterHomogeneity
import EPPAIII.DoubleCover.ClusterComponentEdges

/-!
# Regular unions of cliques are homogeneous

An arbitrary finite disjoint union of cliques with equal vertex
degrees is homogeneous. The closed-twin quotient has uniform
clique-fibre cardinalities; extend partial automorphisms by
permuting fibres and their vertices.

No vertex-transitivity, EPPA, Gardiner classification, or
external homogeneous-graph classification is assumed.
-/

namespace EPPAIII.BlockSystems

open EPPAIII.CliqueCovers
open EPPAIII.TwoGraphs

/-- A finite regular disjoint union of cliques is homogeneous. -/
theorem cluster_equal_degrees_isHomogeneous
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hCluster : IsClusterGraph G)
    (hDegrees : ∀ x y : V,
      (DoubleCover.clusterBaseNeighbours G x).card =
        (DoubleCover.clusterBaseNeighbours G y).card) :
    DoubleCover.IsHomogeneousGraph G := by
  classical
  by_cases hV : Nonempty V
  · obtain ⟨anchor⟩ := hV
    let B := ClosedTwinQuotient G
    letI : Fintype B := Fintype.ofFinite B
    letI : DecidableEq B := Classical.decEq B
    let f : V → B := fun x => Quotient.mk (closedTwinSetoid G) x
    let t : ℕ := (DoubleCover.clusterBaseNeighbours G anchor).card + 1
    have hFibreIff (x y : V) :
        f y = f x ↔ y ∈ DoubleCover.clusterBaseComponent G x := by
      rw [DoubleCover.mem_clusterBaseComponent_iff]
      have hAdj := cluster_adj_iff_closed_twin_fibre G hCluster x y
      change G.Adj x y ↔ f x = f y ∧ x ≠ y at hAdj
      constructor
      · intro h
        by_cases hyx : y = x
        · exact Or.inl hyx
        · exact Or.inr (hAdj.mpr ⟨h.symm, fun hxy => hyx hxy.symm⟩)
      · rintro (h | h)
        · subst y
          rfl
        · exact (hAdj.mp h).1.symm
    have hFibreCard (x : V) :
        Fintype.card {v : V // f v = f x} =
          (DoubleCover.clusterBaseComponent G x).card := by
      let E : {v : V // f v = f x} ≃
          {v : V // v ∈ DoubleCover.clusterBaseComponent G x} :=
        { toFun := fun z => ⟨z.1, (hFibreIff x z.1).mp z.2⟩
          invFun := fun z => ⟨z.1, (hFibreIff x z.1).mpr z.2⟩
          left_inv := by intro z; cases z; rfl
          right_inv := by intro z; cases z; rfl }
      calc
        Fintype.card {v : V // f v = f x} =
          Fintype.card {v : V // v ∈ DoubleCover.clusterBaseComponent G x} :=
            Fintype.card_congr E
        _ = (DoubleCover.clusterBaseComponent G x).card := by
          rw [Fintype.card_coe]
    have hCompCard (x : V) :
        (DoubleCover.clusterBaseComponent G x).card =
          (DoubleCover.clusterBaseNeighbours G x).card + 1 := by
      have hx : x ∉ DoubleCover.clusterBaseNeighbours G x := by
        simp [DoubleCover.clusterBaseNeighbours]
      unfold DoubleCover.clusterBaseComponent
      rw [Finset.card_insert_of_notMem hx]
      omega
    have hCard : ∀ b : B,
        Fintype.card {v : V // f v = b} = t := by
      intro b
      refine Quotient.inductionOn b ?_
      intro x
      change Fintype.card {v : V // f v = f x} = t
      calc
        Fintype.card {v : V // f v = f x} =
          (DoubleCover.clusterBaseComponent G x).card := hFibreCard x
        _ = (DoubleCover.clusterBaseNeighbours G x).card + 1 := hCompCard x
        _ = t := by rw [hDegrees x anchor]
    have hAdj (x y : V) :
        G.Adj x y ↔ f x = f y ∧ x ≠ y :=
      cluster_adj_iff_closed_twin_fibre G hCluster x y
    exact homogeneous_of_uniform_complete_fibres G f t hCard hAdj
  · intro D p _
    refine ⟨Equiv.refl V, ?_, ?_⟩
    · intro x y
      exact (hV ⟨x⟩).elim
    · intro x _
      exact (hV ⟨x⟩).elim

/-- A finite cluster graph is either homogeneous or has vertices
of different degrees. -/
theorem cluster_homogeneous_or_unequal_degrees
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hCluster : IsClusterGraph G) :
    DoubleCover.IsHomogeneousGraph G ∨
      ∃ x y : V,
        (DoubleCover.clusterBaseNeighbours G x).card ≠
          (DoubleCover.clusterBaseNeighbours G y).card := by
  classical
  by_cases hEqual : ∀ x y : V,
      (DoubleCover.clusterBaseNeighbours G x).card =
        (DoubleCover.clusterBaseNeighbours G y).card
  · exact Or.inl (cluster_equal_degrees_isHomogeneous G hCluster hEqual)
  · right
    push_neg at hEqual
    exact hEqual

end EPPAIII.BlockSystems
