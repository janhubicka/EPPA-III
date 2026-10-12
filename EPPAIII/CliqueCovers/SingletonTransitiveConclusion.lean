import EPPAIII.CliqueCovers.SingletonOutsideRigidity
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges

/-!
# Complete one-partial singleton outside graph classification

In a vertex-transitive host, the two equal halves of a double-sized
EPPA witness have equal numbers of induced edges. The natural wreath
action on the saturated singleton profile choices then forces the
induced complementary graph to be exactly sK_t.

Neither an a priori outside-clique partition nor coherent EPPA
extensions are assumed. This closes the *outside graph* step for
a unique singleton partial coordinate in Section 3. The subsequent
uniform cross-block connection statement is a separate task.
-/

namespace EPPAIII.CliqueCovers

/-- If one outside vertex has precisely one size-one coordinate and
the witness is vertex-transitive of order 2st, then the entire
complementary half is s disjoint K_t cliques in its canonical
singleton-profile labels. -/
theorem eppa_singleton_outside_eq_cliqueUnion_of_transitive {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    (outsideInducedGraph H e).comap
      (saturatedSingletonOutsideEquiv
        H e heppa hOrder w hw hUnique) = cliqueUnion s t := by
  classical
  let label := saturatedSingletonOutsideEquiv
    H e heppa hOrder w hw hUnique
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
  exact eppa_singleton_outside_eq_cliqueUnion_of_equal_edges
    H e heppa hOrder w hw hUnique hs ht hEdges

end EPPAIII.CliqueCovers
