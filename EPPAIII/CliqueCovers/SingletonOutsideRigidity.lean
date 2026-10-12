import EPPAIII.CliqueCovers.SingletonOutsideAction
import EPPAIII.CliqueCovers.EquivariantWreathAssembly

/-!
# Classification of the actual outside induced graph: singleton case

This composes the saturated EPPA action from SingletonOutsideAction
with the abstract equivariant wreath graph rigidity theorem.

The unique remaining numerical hypothesis is the half-edge-count
equality; for a vertex-transitive graph with equal halves it follows
from regularity and double-counting the cross edges, but the
transport from an arbitrary host vertex type has its own Lean
interface and is NOT assumed proved here.

No outside clique partition or coherent EPPA lifts are assumed.
-/

namespace EPPAIII.CliqueCovers

/-- A double-sized EPPA witness whose outside profile orbit has one
singleton coordinate has outside graph exactly sK_t, PROVIDED its
outside graph has the same number of edges as the base half. This
precisely packages the proved symmetry part of Lemma 3.7 and
isolates only the regular equal-half count. -/
theorem eppa_singleton_outside_eq_cliqueUnion_of_equal_edges {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    [DecidableRel
      ((outsideInducedGraph H e).comap
        (saturatedSingletonOutsideEquiv
          H e heppa hOrder w hw hUnique)).Adj]
    [DecidableRel (cliqueUnion s t).Adj]
    (hEdges :
      (((outsideInducedGraph H e).comap
        (saturatedSingletonOutsideEquiv
          H e heppa hOrder w hw hUnique)).edgeFinset).card =
        (cliqueUnion s t).edgeFinset.card) :
    (outsideInducedGraph H e).comap
      (saturatedSingletonOutsideEquiv
        H e heppa hOrder w hw hUnique) = cliqueUnion s t := by
  classical
  apply graph_eq_cliqueUnion_of_equivariant_wreath_label
    (outsideInducedGraph H e)
    (saturatedSingletonOutsideEquiv H e heppa hOrder
      w hw hUnique) hs ht ?_ hEdges
  intro outer inner
  exact eppa_singleton_outside_has_natural_wreath_action
    H e heppa hOrder w hw hUnique outer inner

end EPPAIII.CliqueCovers
