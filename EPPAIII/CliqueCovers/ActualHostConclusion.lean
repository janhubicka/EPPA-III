import EPPAIII.CliqueCovers.ClusterHostClassification
import EPPAIII.CliqueCovers.NonclusterEqualCliqueConclusion
import EPPAIII.CliqueCovers.DegenerateOutside
import EPPAIII.BlockSystems.GraphTransport

/-!
# Actual-host classification from the manuscript's two halves

The selected embedding is fixed, and an outside equivalence witnesses
that the complementary half is sK_t. In the cluster case, the
cross-block matching theorem gives a cover without transitivity.
In the non-cluster case (s,t≥2), the stronger profile theorem even
does not need the outside equivalence.

No Gardiner, rank-three, or other external classification is invoked.
-/

namespace EPPAIII.CliqueCovers

/-- A cluster EPPA host whose designated two halves are both
unions of s equal cliques is a uniform generalised clique cover.
The equivalence fixes the selected half pointwise. -/
theorem eppa_cluster_actual_host_is_uniform_cover {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hCluster : EPPAIII.BlockSystems.IsClusterGraph H)
    (outside : (Fin s × Fin t) ≃
      {w : W // w ∈ finiteOutside e})
    (hOutside : (outsideInducedGraph H e).comap outside =
      cliqueUnion s t) :
    ∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin t, phi (false,x) = e x) ∧
      H.comap phi = coverGraph s t X Y := by
  classical
  let phi₀ : CoverVertex s t ≃ W := balancedHostEquiv e outside
  have hBottom (x : Fin s × Fin t) :
      phi₀ (false,x) = e x := balancedHostEquiv_false e outside x
  have hEppa : IsEPPAEmbedding (cliqueUnion s t)
      (H.comap phi₀) (coverLeftEmbedding s t) := by
    have h := EPPAIII.BlockSystems.eppa_pullback_bottom
      (cliqueUnion s t) H e heppa phi₀ hBottom
    change IsEPPAEmbedding (cliqueUnion s t)
      (H.comap phi₀) (coverLeftEmbedding s t) at h
    exact h
  have hRight (i j : Fin s) (a b : Fin t) :
      (H.comap phi₀).Adj (right i a) (right j b) ↔
        i = j ∧ a ≠ b := by
    have h : ((outsideInducedGraph H e).comap outside).Adj
        (i,a) (j,b) ↔ (cliqueUnion s t).Adj (i,a) (j,b) := by
      rw [hOutside]
    change H.Adj (outside (i,a)).val (outside (j,b)).val ↔
      (i = j ∧ a ≠ b) at h
    change H.Adj (phi₀ (right i a)) (phi₀ (right j b)) ↔
      (i = j ∧ a ≠ b)
    exact h
  have hClusterPull : EPPAIII.BlockSystems.IsClusterGraph
      (H.comap phi₀) := by
    intro a b c hab hbc hac
    exact hCluster (phi₀ a) (phi₀ b) (phi₀ c)
      hab hbc (phi₀.injective.ne hac)
  rcases eppa_cluster_host_full_or_empty
      (H.comap phi₀) hEppa hRight hClusterPull with hNone | ⟨p,hPair⟩
  · exact ⟨phi₀,.empty,false,hBottom,hNone⟩
  · let phi : CoverVertex s t ≃ W :=
      (rightCliqueReindex p).trans phi₀
    refine ⟨phi,.full,false,?_,?_⟩
    · intro x
      change phi₀ (rightCliqueReindex p (false,x)) = e x
      simpa [rightCliqueReindex] using hBottom x
    · change (H.comap phi₀).comap (rightCliqueReindex p) =
        coverGraph s t .full false
      exact hPair

/-- The exact two-half version of Lemma 6.1 for s,t≥2, with
the outside clique partition explicitly witnessed.
The result is stronger than the source: imprimitive H is not assumed. -/
theorem eppa_equal_clique_double_classification {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (outside : (Fin s × Fin t) ≃
      {w : W // w ∈ finiteOutside e})
    (hOutside : (outsideInducedGraph H e).comap outside =
      cliqueUnion s t) :
    (∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin t, phi (false,x) = e x) ∧
      H.comap phi = coverGraph s t X Y) ∨
    (s = 2 ∧ t = 2 ∧
      ∃ phi : CoverVertex 2 2 ≃ W,
        (∀ x : Fin 2 × Fin 2, phi (false,x) = e x) ∧
        H.comap phi = wagnerCanonicalGraph) := by
  by_cases hCluster : EPPAIII.BlockSystems.IsClusterGraph H
  · left
    exact eppa_cluster_actual_host_is_uniform_cover
      H e heppa hCluster outside hOutside
  · exact eppa_noncluster_equal_clique_full_classification_fixed_base
      H e heppa hs ht hOrder hTransitive hCluster

end EPPAIII.CliqueCovers
