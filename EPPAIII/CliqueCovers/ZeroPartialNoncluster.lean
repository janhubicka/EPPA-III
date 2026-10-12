import EPPAIII.CliqueCovers.ZeroPartialClassSize
import EPPAIII.CliqueCovers.NonclusterQuotient

/-!
# Exact twin class size for non-cluster zero-partial witnesses

The graph-theoretic class-size result previously required the
canonical twin quotient to contain an edge. We now discharge this
hypothesis directly from non-cluster status of the host:
a non-cluster graph has an edge between different twin classes.

This removes the remaining positive-degree qualification from the
zero-partial numerical part of the direct proof of Lemma 3.7.

The further deduction that a non-homogeneous vertex-transitive host
cannot be a cluster graph remains a separate homogeneous-graph
classification step, treated at paper level.
-/

namespace EPPAIII.CliqueCovers

/-- In a non-cluster, vertex-transitive host of order 2st with no
partial outside coordinates, the quotient consists of exactly 2s
classes and the class containing any selected clique has size t. -/
theorem zero_partial_exact_twin_size_of_noncluster {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (hs : 0 < s) (ht : 0 < t)
    (hHostCard : Fintype.card W = 2 * s * t)
    (hTransitive : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧ q u = v)
    [Fintype (ClosedTwinQuotient H)]
    [DecidableRel (closedTwinQuotientGraph H).Adj]
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H)
    (i : Fin s) (a : Fin t) :
    Fintype.card (ClosedTwinQuotient H) = 2 * s ∧
      (closedTwinClass H (e (i,a))).card = t := by
  exact zero_partial_exact_twin_class_size
    H e he hNoPartial hs ht hHostCard hTransitive
    (noncluster_twin_quotient_has_edge H hNonCluster) i a

end EPPAIII.CliqueCovers
