import EPPAIII.BlockSystems.TransitiveClusterHomogeneity
import EPPAIII.BlockSystems.TransitiveSeparatedHalf
import EPPAIII.DoubleCover.HomogeneityComplement

/-!
# Imprimitive rank-three actions have homogeneous host graphs

A rank-three permutation action has at most one orbit on ordered
edges and at most one on ordered distinct nonedges. If this
action also preserves a nontrivial equivalence relation, then
the relation is forced to be adjacency or nonadjacency
(on distinct pairs). Consequently the graph is a union of
cliques or the complement of such a union.

This is the elementary rank-three step in the strict-inequality
part of Proposition 6.17. It avoids invoking a classification
of rank-three graphs, keeping separate the earlier proposition
which supplies the rank-three hypothesis when |H| < 2|G|.
-/

namespace EPPAIII.BlockSystems

/-- Each ordered pair of distinct vertices is in the same
automorphism orbit as every other pair of the same adjacency
status. This is the rank-three edge/nonedge orbit property
used by the manuscript (without naming any classified graph). -/
def HasOrderedPairOrbitByStatus {W : Type*}
    (H : SimpleGraph W) : Prop :=
  ∀ u v u' v' : W, u ≠ v → u' ≠ v' →
    (H.Adj u v ↔ H.Adj u' v') →
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧
        q u = u' ∧ q v = v'

/-- An invariant block relation has constant truth value on
each orbit of ordered edges and each orbit of ordered
distinct nonedges. -/
theorem block_relation_of_same_pair_status
    {W B : Type*} (H : SimpleGraph W)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hPairOrbits : HasOrderedPairOrbitByStatus H)
    (u v u' v' : W)
    (huv : u ≠ v) (huv' : u' ≠ v')
    (hStatus : H.Adj u v ↔ H.Adj u' v') :
    (block u = block v ↔ block u' = block v') := by
  obtain ⟨q,hq,hqu,hqv⟩ :=
    hPairOrbits u v u' v' huv huv' hStatus
  simpa only [hqu,hqv] using (hBlocks q hq u v)

/-- A genuinely nontrivial invariant partition under the
rank-three ordered-pair-orbit condition makes the graph
a clique union or the complement of a clique union.
No graph or permutation-group classification is used. -/
theorem rank_three_imprimitive_cluster_or_cocluster
    {W B : Type*} (H : SimpleGraph W)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hPairOrbits : HasOrderedPairOrbitByStatus H)
    (hInside : ∃ a b : W, a ≠ b ∧ block a = block b)
    (hOutside : ∃ c d : W, block c ≠ block d) :
    IsClusterGraph H ∨ IsCoClusterGraph H := by
  obtain ⟨a,b,hab,hSame⟩ := hInside
  obtain ⟨c,d,hDiff⟩ := hOutside
  have hcd : c ≠ d := by
    intro h
    exact hDiff (congrArg block h)
  by_cases hAdj : H.Adj a b
  · have hNotCD : ¬ H.Adj c d := by
      intro hCD
      have hStatus : H.Adj a b ↔ H.Adj c d :=
        ⟨fun _ => hCD, fun _ => hAdj⟩
      exact hDiff
        ((block_relation_of_same_pair_status H block hBlocks
          hPairOrbits a b c d hab hcd hStatus).mp hSame)
    left
    intro u v w huv hvw huw
    have hUV : block u = block v := by
      have hStatus : H.Adj a b ↔ H.Adj u v :=
        ⟨fun _ => huv, fun _ => hAdj⟩
      exact (block_relation_of_same_pair_status H block hBlocks
        hPairOrbits a b u v hab (H.ne_of_adj huv) hStatus).mp hSame
    have hVW : block v = block w := by
      have hStatus : H.Adj a b ↔ H.Adj v w :=
        ⟨fun _ => hvw, fun _ => hAdj⟩
      exact (block_relation_of_same_pair_status H block hBlocks
        hPairOrbits a b v w hab (H.ne_of_adj hvw) hStatus).mp hSame
    by_contra hNotUW
    have hStatus : H.Adj u w ↔ H.Adj c d :=
      ⟨fun h => False.elim (hNotUW h),
        fun h => False.elim (hNotCD h)⟩
    exact hDiff
      ((block_relation_of_same_pair_status H block hBlocks
        hPairOrbits u w c d huw hcd hStatus).mp (hUV.trans hVW))
  · have hCD : H.Adj c d := by
      by_contra hNotCD
      have hStatus : H.Adj a b ↔ H.Adj c d :=
        ⟨fun h => False.elim (hAdj h),
          fun h => False.elim (hNotCD h)⟩
      exact hDiff
        ((block_relation_of_same_pair_status H block hBlocks
          hPairOrbits a b c d hab hcd hStatus).mp hSame)
    right
    intro u v w huv hvw huw hNotUV hNotVW
    have hUV : block u = block v := by
      have hStatus : H.Adj a b ↔ H.Adj u v :=
        ⟨fun h => False.elim (hAdj h),
          fun h => False.elim (hNotUV h)⟩
      exact (block_relation_of_same_pair_status H block hBlocks
        hPairOrbits a b u v hab huv hStatus).mp hSame
    have hVW : block v = block w := by
      have hStatus : H.Adj a b ↔ H.Adj v w :=
        ⟨fun h => False.elim (hAdj h),
          fun h => False.elim (hNotVW h)⟩
      exact (block_relation_of_same_pair_status H block hBlocks
        hPairOrbits a b v w hab hvw hStatus).mp hSame
    intro hAdjUW
    have hStatus : H.Adj u w ↔ H.Adj c d :=
      ⟨fun _ => hCD, fun _ => hAdjUW⟩
    exact hDiff
      ((block_relation_of_same_pair_status H block hBlocks
        hPairOrbits u w c d huw hcd hStatus).mp (hUV.trans hVW))

/-- Rank-three ordered pair orbits plus vertex transitivity
and nontrivial imprimitivity force the host to be homogeneous.
This closes the elementary rank-three step in the strict-order
case, conditional on the earlier small-witness rank-three theorem. -/
theorem transitive_rank_three_imprimitive_isHomogeneous
    {W B : Type*} [Fintype W]
    (H : SimpleGraph W)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPairOrbits : HasOrderedPairOrbitByStatus H)
    (hInside : ∃ a b : W, a ≠ b ∧ block a = block b)
    (hOutside : ∃ c d : W, block c ≠ block d) :
    EPPAIII.DoubleCover.IsHomogeneousGraph H := by
  rcases rank_three_imprimitive_cluster_or_cocluster
      H block hBlocks hPairOrbits hInside hOutside with
    hCluster | hCoCluster
  · exact vertex_transitive_cluster_isHomogeneous
      H hTrans hCluster
  · have hClusterComplement : IsClusterGraph Hᶜ := by
      intro a b c hab hbc hac
      change a ≠ b ∧ ¬ H.Adj a b at hab
      change b ≠ c ∧ ¬ H.Adj b c at hbc
      change a ≠ c ∧ ¬ H.Adj a c
      exact ⟨hac,hCoCluster a b c hab.1 hbc.1
        hac hab.2 hbc.2⟩
    have hTransComplement :
        EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms Hᶜ :=
      transitive_complement H hTrans
    exact (EPPAIII.DoubleCover.homogeneous_complement_iff H).mpr
      (vertex_transitive_cluster_isHomogeneous
        Hᶜ hTransComplement hClusterComplement)

end EPPAIII.BlockSystems
