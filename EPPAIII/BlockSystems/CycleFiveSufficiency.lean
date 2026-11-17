import EPPAIII.BlockSystems.ImprimitiveSufficiencyLifts
import EPPAIII.BlockSystems.CycleFiveDoubleClassification

/-!
# Independent finite homogeneity certificate for the selected five-cycle

The graph-specific homogeneity input for the generic sufficiency
construction is proved by a finite computation in the Lean kernel.
There is no Gardiner hypothesis.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- Every partial automorphism of the five-cycle extends to a
dihedral automorphism of the five-cycle, verified as a finite
decidable proposition. -/
theorem cycleFive_isHomogeneous :
    DoubleCover.IsHomogeneousGraph (SimpleGraph.cycleGraph 5) := by
  letI : DecidableRel (SimpleGraph.cycleGraph 5).Adj :=
    fun x y => decidable_of_iff
      (cycleFiveExplicitAdjacent x y)
      (cycleFiveExplicitAdjacent_iff x y)
  decide

/-- Unconditional EPPA sufficiency of the five-cycle's disjoint double. -/
theorem cycleFive_separated_double_eppa :
    IsEPPAEmbedding
      (SimpleGraph.cycleGraph 5)
      (separatedDoubleGraph (SimpleGraph.cycleGraph 5))
      (DoubleCover.bottomEmbedding (Fin 5)) :=
  homogeneous_base_separated_double_eppa
    (SimpleGraph.cycleGraph 5) cycleFive_isHomogeneous

/-- Unconditional EPPA sufficiency of the canonical five-cycle Taylor double. -/
theorem cycleFive_taylor_double_eppa :
    IsEPPAEmbedding
      (SimpleGraph.cycleGraph 5)
      (EPPAIII.TwoGraphs.taylorPairGraph (SimpleGraph.cycleGraph 5))
      (DoubleCover.bottomEmbedding (Fin 5)) :=
  homogeneous_base_taylor_double_eppa
    (SimpleGraph.cycleGraph 5) cycleFive_isHomogeneous

/-- Unconditional EPPA sufficiency of the matching five-cycle prism. -/
theorem cycleFive_matching_prism_eppa :
    IsEPPAEmbedding
      (SimpleGraph.cycleGraph 5)
      (matchedLayerGraph
        (SimpleGraph.cycleGraph 5) (SimpleGraph.cycleGraph 5))
      (DoubleCover.bottomEmbedding (Fin 5)) :=
  homogeneous_base_matching_prism_eppa
    (SimpleGraph.cycleGraph 5) cycleFive_isHomogeneous

/-- The twin blow-up is another five-cycle EPPA host. -/
theorem cycleFive_twin_blowup_eppa :
    IsEPPAEmbedding
      (SimpleGraph.cycleGraph 5)
      (twinBlowupGraph (SimpleGraph.cycleGraph 5))
      (DoubleCover.bottomEmbedding (Fin 5)) :=
  homogeneous_base_twin_blowup_eppa
    (SimpleGraph.cycleGraph 5) cycleFive_isHomogeneous

end EPPAIII.BlockSystems
