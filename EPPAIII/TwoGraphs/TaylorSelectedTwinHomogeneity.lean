import EPPAIII.TwoGraphs.TaylorSelectedTwinEquality
import EPPAIII.TwoGraphs.FullSelectedTwinFibres
import EPPAIII.TwoGraphs.UniformFibreHomogeneity
import EPPAIII.TwoGraphs.EPPAEdgeTwinPropagation

/-!
# Selected true-twin edge forces homogeneous Taylor base

The first case of the true-twin quotient argument in Section 5:
two selected adjacent vertices are true twins in the Taylor EPPA
host. EPPA transports the true-twin property to all selected edges,
so quotient classes occupied by the base form an independent set.
The positive regular quotient and finite class-size count yield
equality in the occupancy bound. Every selected occupied class
is therefore full; the base is a disjoint union of equally sized
cliques, and is homogeneous. No exact quotient degree is needed.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- Under the nontriviality witness of an even triple,
any selected true-twin edge in a vertex-transitive Taylor
EPPA witness forces the selected graph to be homogeneous. -/
theorem taylor_eppa_selected_true_twin_edge_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    [Fintype (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (closedTwinQuotientGraph (taylorPairGraph G)).Adj]
    (heppa : IsEPPAEmbedding G
      (taylorPairGraph G) (EPPAIII.DoubleCover.bottomEmbedding V))
    (hTrans : HasTransitiveGraphAutomorphisms (taylorPairGraph G))
    (hEven : ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EvenTriple G x y z)
    (x y : V) (hXY : G.Adj x y)
    (hTwin : SameClosedNeighbourhood
      (taylorPairGraph G) (false,x) (false,y)) :
    EPPAIII.DoubleCover.IsHomogeneousGraph G := by
  classical
  let H := taylorPairGraph G
  let Q := ClosedTwinQuotient H
  let π : V → Q := fun u =>
    Quotient.mk (closedTwinSetoid H) (false,u)
  let I : Finset Q := (Finset.univ : Finset V).image π
  let t : ℕ := (closedTwinClass H (false,x)).card
  have hEqual :
      Fintype.card V = I.card * t := by
    simpa only [I,π,Q,H,t] using
      (taylor_selected_twin_occupied_equalities
        G heppa hTrans hEven x y hXY hTwin).1
  have hUniform (w : Bool × V) :
      (closedTwinClass H w).card = t :=
    closedTwinClass_card_of_vertex_transitive
      H hTrans w (false,x)
  have hFull (q : Q) (hq : q ∈ I) :
      ((Finset.univ : Finset V).filter
        (fun v => π v = q)).card = t := by
    have hh := selected_twin_quotient_occupied_class_full
      H (EPPAIII.DoubleCover.bottomEmbedding V)
      t hUniform hEqual q hq
    change ((Finset.univ : Finset V).filter
      (fun v => π v = q)).card = t at hh
    exact hh
  let f : V → I := fun v =>
    ⟨π v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩⟩
  have hFib (q : I) :
      Fintype.card {v : V // f v = q} = t := by
    have hh := hFull q.val q.property
    simpa [Fintype.card_subtype, f, I, π] using hh
  have hAdj (u v : V) :
      G.Adj u v ↔ f u = f v ∧ u ≠ v := by
    constructor
    · intro huv
      have hTwins :=
        eppa_true_twins_propagate_to_all_edges
          G H (EPPAIII.DoubleCover.bottomEmbedding V)
          heppa x y hXY hTwin u v huv
      have hπ : π u = π v := Quotient.sound hTwins
      refine ⟨?_, G.ne_of_adj huv⟩
      exact Subtype.ext hπ
    · rintro ⟨hSame,hNe⟩
      have hπ : π u = π v := congrArg Subtype.val hSame
      have hTwin' : SameClosedNeighbourhood
          H (false,u) (false,v) := Quotient.exact hπ
      have hUnequal : (false,u) ≠ (false,v) := by
        intro h
        exact hNe (congrArg Prod.snd h)
      have hHostEdge :=
        adjacent_of_same_closed_neighbourhood
          H (false,u) (false,v) hUnequal hTwin'
      exact (heppa.1 u v).mpr hHostEdge
  exact homogeneous_of_uniform_complete_fibres
    G f t hFib hAdj

end EPPAIII.TwoGraphs
