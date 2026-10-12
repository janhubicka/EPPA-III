import EPPAIII.CliqueCovers.CoSingletonOutsideRigidity
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges

/-!
# Complete co-singleton one-partial outside graph classification

The inside and outside halves have equal internal edge counts in a
vertex-transitive host. The canonical outside labels for a unique
size-(t-1) coordinate are its index and omitted point; actual EPPA
extensions induce the natural wreath action on them. Consequently
the complementary induced graph is sK_t.

No outside clique decomposition is assumed. The off-diagonal
cross-block uniformity will be proved separately.
-/

namespace EPPAIII.CliqueCovers

/-- The co-singleton one-partial case forces the complementary half
to be a union of s disjoint t-cliques. -/
theorem eppa_cosingleton_outside_eq_cliqueUnion_of_transitive {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    (outsideInducedGraph H e).comap
      (saturatedCoSingletonOutsideEquiv
        H e heppa hOrder (by omega) w hw hUnique) = cliqueUnion s t := by
  classical
  have htPositive : 0 < t := by omega
  let label := saturatedCoSingletonOutsideEquiv
    H e heppa hOrder htPositive w hw hUnique
  letI : Nonempty (Fin s × Fin t) :=
    ⟨(⟨0, by omega⟩,⟨0, by omega⟩)⟩
  have hIntrinsic :
      ((outsideInducedGraph H e).comap label).edgeSet.ncard =
        (cliqueUnion s t).edgeSet.ncard :=
    arbitrary_host_outside_edge_count_eq_base
      (cliqueUnion s t) H e heppa.1 label hTransitive
  have hEdges :
      ((outsideInducedGraph H e).comap label).edgeFinset.card =
        (cliqueUnion s t).edgeFinset.card := by
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hIntrinsic
  exact eppa_cosingleton_outside_eq_cliqueUnion_of_equal_edges
    H e heppa hOrder w hw hUnique hs ht hEdges

end EPPAIII.CliqueCovers
