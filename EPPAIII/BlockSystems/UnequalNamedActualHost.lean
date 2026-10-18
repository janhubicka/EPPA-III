import EPPAIII.BlockSystems.TwoCliqueColourFromComponents
import EPPAIII.BlockSystems.UnequalFinalTaylor

/-!
# Source-facing final classification of actual unequal-clique EPPA hosts

The verified actual-host theorem yields the no-third-component
conclusion, an equivalence fixing the selected base, all Taylor
inter-fibre adjacency entries and the uniform mate bit.

This combines the canonical Boolean colouring from the component
exhaustion with the named matched-double identification, and
transports the genuine non-cluster hypothesis through that
equivalence. No pre-labelled outside copy, coherent EPPA
extensions, or graph-classification theorem is assumed.

The manuscript's non-homogeneous-to-non-cluster implication is
an elementary separate paper bridge; we retain the exact
non-cluster hypothesis of the existing Lean construction.
-/

namespace EPPAIII.BlockSystems

/-- Complete unequal-clique conclusion for an actual finite
vertex-transitive imprimitive EPPA host, with its fixed selected copy:
the designated base is exactly two cliques and the host is exactly
two complete graphs joined by a perfect matching, after the
canonical Taylor coordinate change. -/
theorem transitive_eppa_unequal_two_cliques_named_host
    {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hNonCluster : ¬ IsClusterGraph H)
    (hCluster : IsClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    ∃ (c : V → Bool) (φ : Bool × V ≃ W),
      G = twoCliqueGraph c ∧
      (∀ v : V, φ (false,v) = e v) ∧
      pullbackGraph H φ = twoCliqueMatchedGraph c true := by
  classical
  obtain ⟨hCover, ⟨φ, hBase, ⟨mate, hMate, hPattern⟩⟩⟩ :=
    transitive_eppa_unequal_two_cliques_and_taylor
      G H e heppa block hBlocks hSurj hTrans
      hNonCluster hCluster hManyBlocks hNontrivial
      hHostSize x y hDifferent
  obtain ⟨c,hEqG⟩ :=
    cluster_two_components_has_twoClique_colouring
      G hCluster x y hCover
  have hBottom (u v : V) :
      (pullbackGraph H φ).Adj (false,u) (false,v) ↔
        (twoCliqueGraph c).Adj u v := by
    change H.Adj (φ (false,u)) (φ (false,v)) ↔
      (twoCliqueGraph c).Adj u v
    rw [hBase u, hBase v]
    simpa only [hEqG] using (heppa.1 u v).symm
  have hMate' (v : V) :
      (pullbackGraph H φ).Adj (false,v) (true,v) ↔
        mate = true := by
    change H.Adj (φ (false,v)) (φ (true,v)) ↔ mate = true
    exact hMate v
  have hPattern' :
      DoubleCover.RepresentsPairPattern
        (twoCliqueGraph c) (pullbackGraph H φ)
        DoubleCover.taylor := by
    simpa only [← hEqG] using hPattern
  have hNonCluster' :
      ¬ IsClusterGraph (pullbackGraph H φ) := by
    intro hCluster'
    apply hNonCluster
    intro u v w huv hvw huw
    have huv' :
        (pullbackGraph H φ).Adj (φ.symm u) (φ.symm v) := by
      change H.Adj (φ (φ.symm u)) (φ (φ.symm v))
      simpa using huv
    have hvw' :
        (pullbackGraph H φ).Adj (φ.symm v) (φ.symm w) := by
      change H.Adj (φ (φ.symm v)) (φ (φ.symm w))
      simpa using hvw
    have huw' : φ.symm u ≠ φ.symm w := by
      intro h
      apply huw
      have hh := congrArg φ h
      simpa using hh
    have hUw := hCluster' (φ.symm u) (φ.symm v)
      (φ.symm w) huv' hvw' huw'
    change H.Adj (φ (φ.symm u)) (φ (φ.symm w)) at hUw
    simpa using hUw
  have hNamed :
      pullbackGraph H φ = twoCliqueMatchedGraph c true :=
    twoClique_actual_taylor_noncluster_is_matched
      c (pullbackGraph H φ) mate
      hBottom hPattern' hMate' hNonCluster'
  exact ⟨c,φ,hEqG,hBase,hNamed⟩

end EPPAIII.BlockSystems
