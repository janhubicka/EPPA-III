import EPPAIII.DoubleCover.TwoPointAction
import EPPAIII.CliqueCovers.TwinClassTransport
import EPPAIII.BlockSystems.ClusterObstructions

/-!
# EPPA propagation of true-twin edges

A delicate source inference in the true-twin quotient proof of
Section 5.1: if one selected edge joins two true twins of the
actual EPPA host, every selected edge must join true twins.
This forces the embedded base to be a disjoint union of cliques.

This is a general graph EPPA lemma; it does not use a Taylor
double, any two-graph, transitivity of the witness or graph
classification.
-/

namespace EPPAIII.TwoGraphs

/-- One selected edge whose endpoints are true twins propagates
that property to every selected edge by ordinary two-point EPPA. -/
theorem eppa_true_twins_propagate_to_all_edges
    {V W : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (u v : V) (hUV : G.Adj u v)
    (hTwin : EPPAIII.CliqueCovers.SameClosedNeighbourhood
      H (e u) (e v))
    (x y : V) (hXY : G.Adj x y) :
    EPPAIII.CliqueCovers.SameClosedNeighbourhood
      H (e x) (e y) := by
  classical
  obtain ⟨p,hPX,hPY,hPartial⟩ :=
    EPPAIII.DoubleCover.partial_of_two_maps G x y u v
      (G.ne_of_adj hXY) (G.ne_of_adj hUV)
      ⟨fun _ => hUV, fun _ => hXY⟩
  obtain ⟨q,hq,hExt⟩ :=
    heppa.2 ({x,y} : Finset V) p hPartial
  have hx : q (e x) = e u := by
    have h := hExt x (by simp)
    simpa [hPX] using h
  have hy : q (e y) = e v := by
    have h := hExt y (by simp)
    simpa [hPY] using h
  have hBack :=
    EPPAIII.CliqueCovers.sameClosedNeighbourhood_automorphism
      H q.symm
      (EPPAIII.CliqueCovers.graphAutomorphism_symm H q hq)
      (e u) (e v) hTwin
  have hBX : q.symm (e u) = e x := by
    rw [← hx]
    simp
  have hBY : q.symm (e v) = e y := by
    rw [← hy]
    simp
  simpa only [hBX,hBY] using hBack

/-- A selected true-twin edge forces the embedded graph itself
to be a cluster graph. No assumption of host transitivity is
needed: EPPA on two-point domains suffices. -/
theorem eppa_selected_true_twin_edge_forces_cluster
    {V W : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (u v : V) (hUV : G.Adj u v)
    (hTwin : EPPAIII.CliqueCovers.SameClosedNeighbourhood
      H (e u) (e v)) :
    EPPAIII.BlockSystems.IsClusterGraph G := by
  intro x y z hXY hYZ hXZ
  have hSame :=
    eppa_true_twins_propagate_to_all_edges
      G H e heppa u v hUV hTwin x y hXY
  have hHostYZ : H.Adj (e y) (e z) := (heppa.1 y z).mp hYZ
  have hzIn : e z ∈ EPPAIII.CliqueCovers.closedNeighbourhood H (e y) :=
    Or.inr hHostYZ
  have hXz : e z ∈ EPPAIII.CliqueCovers.closedNeighbourhood H (e x) := by
    rw [hSame]
    exact hzIn
  rcases hXz with hEq | hEdge
  · exact False.elim (hXZ (e.injective hEq.symm))
  · exact (heppa.1 x z).mpr hEdge

end EPPAIII.TwoGraphs
