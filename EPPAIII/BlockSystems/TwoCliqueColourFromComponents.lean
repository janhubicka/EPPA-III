import EPPAIII.BlockSystems.TwoCliqueNonclusterMate
import EPPAIII.DoubleCover.ClusterComponentEdges

/-!
# Canonical two-clique colouring from the base component exhaustion

The actual unequal-clique EPPA classification derives that the
selected cluster graph has at most two connected components:
for some x,y, every z is in the closed component of x or y.

Here we show that this conclusion itself produces a Boolean
two-clique representation, without assuming a preselected
two-clique labelling. This is precisely the remaining
source-facing graph-colouring interface in Lemma 6.6.

No EPPA or automorphism argument is used in this last step.
-/

namespace EPPAIII.BlockSystems

/-- A cluster graph whose vertices lie in two specified complete
components is exactly a two-clique graph for a Boolean colouring.
Either component may be empty or equal to the other; the theorem
does not require those exceptional possibilities to be excluded. -/
theorem cluster_two_components_has_twoClique_colouring
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hCluster : IsClusterGraph G)
    (x y : V)
    (hCover : ∀ z : V,
      (z = x ∨ G.Adj x z) ∨
      (z = y ∨ G.Adj y z)) :
    ∃ c : V → Bool, G = twoCliqueGraph c := by
  classical
  let Cx : Finset V := DoubleCover.clusterBaseComponent G x
  let Cy : Finset V := DoubleCover.clusterBaseComponent G y
  let c : V → Bool := fun z => decide (z ∈ Cx)
  have hOther (z : V) (hz : z ∉ Cx) : z ∈ Cy := by
    rcases hCover z with hx | hy
    · have hzx : z ∈ Cx :=
        (DoubleCover.mem_clusterBaseComponent_iff G x z).mpr hx
      exact False.elim (hz hzx)
    · exact (DoubleCover.mem_clusterBaseComponent_iff G y z).mpr hy
  refine ⟨c, ?_⟩
  apply SimpleGraph.ext
  funext z w
  apply propext
  constructor
  · intro hzw
    have hne : z ≠ w := G.ne_of_adj hzw
    have hStatus : (z ∈ Cx ↔ w ∈ Cx) :=
      DoubleCover.clusterBaseComponent_edge_iff
        G hCluster x z w hzw
    have hc : c z = c w := by
      by_cases hz : z ∈ Cx
      · have hw : w ∈ Cx := hStatus.mp hz
        simp [c,hz,hw]
      · have hw : w ∉ Cx := by
          intro hw
          exact hz (hStatus.mpr hw)
        simp [c,hz,hw]
    exact ⟨hne,hc⟩
  · intro h
    have hne : z ≠ w := h.1
    have hc : c z = c w := h.2
    by_cases hz : z ∈ Cx
    · by_cases hw : w ∈ Cx
      · exact DoubleCover.clusterBaseComponent_complete
          G hCluster x z w hz hw hne
      · have hDifferent : c z ≠ c w := by simp [c,hz,hw]
        exact False.elim (hDifferent hc)
    · by_cases hw : w ∈ Cx
      · have hDifferent : c z ≠ c w := by simp [c,hz,hw]
        exact False.elim (hDifferent hc)
      · exact DoubleCover.clusterBaseComponent_complete
          G hCluster y z w
          (hOther z hz) (hOther w hw) hne

end EPPAIII.BlockSystems
