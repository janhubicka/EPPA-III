import EPPAIII.CliqueCovers.CoSingletonOutsideAction
import EPPAIII.CliqueCovers.EquivariantWreathAssembly

/-!
# Classification of the actual complementary graph: co-singleton case

The verified natural outside action in omitted-point labels, combined
with abstract wreath graph rigidity, identifies the induced outside
graph with sK_t whenever its internal edge count equals that of the
selected sK_t. The latter numerical premise follows separately from
host vertex-transitivity, and is not silently assumed here.
-/

namespace EPPAIII.CliqueCovers

theorem eppa_cosingleton_outside_eq_cliqueUnion_of_equal_edges {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    [DecidableRel
      ((outsideInducedGraph H e).comap
        (saturatedCoSingletonOutsideEquiv
          H e heppa hOrder (by omega) w hw hUnique)).Adj]
    [DecidableRel (cliqueUnion s t).Adj]
    (hEdges :
      (((outsideInducedGraph H e).comap
        (saturatedCoSingletonOutsideEquiv
          H e heppa hOrder (by omega) w hw hUnique)).edgeFinset).card =
        (cliqueUnion s t).edgeFinset.card) :
    (outsideInducedGraph H e).comap
      (saturatedCoSingletonOutsideEquiv
        H e heppa hOrder (by omega) w hw hUnique) = cliqueUnion s t := by
  classical
  apply graph_eq_cliqueUnion_of_equivariant_wreath_label
    (outsideInducedGraph H e)
    (saturatedCoSingletonOutsideEquiv H e heppa hOrder
      (by omega) w hw hUnique) hs ht ?_ hEdges
  intro outer inner
  exact eppa_cosingleton_outside_has_natural_wreath_action
    H e heppa hOrder (by omega) w hw hUnique outer inner

end EPPAIII.CliqueCovers
