import EPPAIII.CliqueCovers.ZeroPartialClassSize
import EPPAIII.BlockSystems.ClusterObstructions

/-!
# A positive twin quotient is automatic outside the cluster-graph case

If the canonical quotient graph has no edges, every original host
edge stays within a closed-neighbourhood equivalence class.
Because equality of closed neighbourhoods is transitive and distinct
vertices of a class are adjacent, H must then be a disjoint union
of cliques (a cluster graph).

Consequently any non-cluster H has an edge between distinct twin
classes. Combining this fact with ZeroPartialClassSize removes the
artificial positive-quotient hypothesis from the true-twin class-size
reduction.

In the final manuscript, the host H is non-homogeneous and transitive.
Such a host cannot be a cluster graph, since a vertex-transitive
cluster graph is a disjoint union of equal cliques and homogeneous.
That last implication is kept separate for a precise Lean audit.
-/

namespace EPPAIII.CliqueCovers

/-- If the twin quotient has no edges, the original host is a
disjoint union of (possibly unequal) cliques. -/
theorem cluster_of_edgeless_closed_twin_quotient {W : Type*}
    (H : SimpleGraph W)
    (hNoEdges : ∀ x y : ClosedTwinQuotient H,
      ¬ (closedTwinQuotientGraph H).Adj x y) :
    EPPAIII.BlockSystems.IsClusterGraph H := by
  intro a b c hab hbc hac
  have hTwinAB : SameClosedNeighbourhood H a b := by
    by_contra hDifferent
    have hEdge :=
      (closedTwinQuotient_adj_mk H a b).mpr ⟨hDifferent, hab⟩
    exact hNoEdges _ _ hEdge
  have hTwinBC : SameClosedNeighbourhood H b c := by
    by_contra hDifferent
    have hEdge :=
      (closedTwinQuotient_adj_mk H b c).mpr ⟨hDifferent, hbc⟩
    exact hNoEdges _ _ hEdge
  have hTwinAC : SameClosedNeighbourhood H a c :=
    hTwinAB.trans hTwinBC
  exact adjacent_of_same_closed_neighbourhood H a c hac hTwinAC

/-- Any non-cluster host has a positive edge between distinct twin classes. -/
theorem closed_twin_quotient_has_edge_of_noncluster {W : Type*}
    (H : SimpleGraph W)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    ∃ x y : ClosedTwinQuotient H,
      (closedTwinQuotientGraph H).Adj x y := by
  by_contra hNo
  push_neg at hNo
  exact hNonCluster (cluster_of_edgeless_closed_twin_quotient H hNo)

/-- The main zero-partial class-size reduction with the natural
non-cluster condition in place of positive quotient degree. -/
theorem zero_partial_exact_twin_class_size_of_noncluster {s t : ℕ}
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
    (closed_twin_quotient_has_edge_of_noncluster H hNonCluster) i a

end EPPAIII.CliqueCovers
