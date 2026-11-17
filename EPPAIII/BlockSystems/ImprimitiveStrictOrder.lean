import EPPAIII.BlockSystems.SmallHostRankThreeFinal
import EPPAIII.BlockSystems.RankThreeActualImprimitiveBlocks

/-!
# The strict-order obstruction in the imprimitive classification

This file assembles the strict-size part of Proposition 6.17 under
precisely the source's actual-host EPPA and invariant-block hypotheses.

One does *not* have to classify imprimitive rank-three groups:
the small-host ordered-pair-orbit theorem supplies two-point orbit
transitivity; a nontrivial Aut(H)-invariant partition then forces a
transitive H to be a cluster or co-cluster graph, hence homogeneous.

The theorem's proof does not use Gardiner, the equal/unequal clique
classifications, a priori outside-half coordinates, or any coherent
EPPA choice. It does not replace the double-order classification.
-/

namespace EPPAIII.BlockSystems

/-- An imprimitive vertex-transitive EPPA host with strictly fewer
than twice as many vertices as its base is homogeneous. The explicit
block data are an actual nontrivial invariant partition of the host. -/
theorem transitive_eppa_strict_imprimitive_host_isHomogeneous
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hStrict : Fintype.card W < 2 * Fintype.card V) :
    EPPAIII.DoubleCover.IsHomogeneousGraph H := by
  have hPairs : HasOrderedPairOrbitByStatus H :=
    transitive_eppa_small_strict_has_pair_orbits
      G H e heppa hTrans hStrict
  exact transitive_rank_three_actual_blocks_isHomogeneous
    H block hBlocks hSurj hTrans hPairs hManyBlocks hNontrivial

/-- Consequently the non-homogeneous imprimitive branch of
Proposition 6.17 has exactly doubled order, provided it is bounded
above by twice the base order. No classification of homogeneous
graphs is needed for this first reduction. -/
theorem nonhomogeneous_imprimitive_eppa_host_exactly_double
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ EPPAIII.DoubleCover.IsHomogeneousGraph H)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hBound : Fintype.card W ≤ 2 * Fintype.card V) :
    Fintype.card W = 2 * Fintype.card V := by
  by_contra hDifferent
  have hStrict : Fintype.card W < 2 * Fintype.card V := by omega
  exact hNonhomogeneous
    (transitive_eppa_strict_imprimitive_host_isHomogeneous
      G H e heppa block hBlocks hSurj hTrans
      hManyBlocks hNontrivial hStrict)

end EPPAIII.BlockSystems
