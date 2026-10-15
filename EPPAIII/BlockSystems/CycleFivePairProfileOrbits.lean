import EPPAIII.BlockSystems.CycleFiveTransitivity
import EPPAIII.BlockSystems.OutsideProfileMultiplicity

/-!
# Pair-profile orbits in the five-cycle

Under the cyclic translations of Fin 5, every unordered pair of
distinct vertices has orbit size five. There are exactly two such
orbits, adjacent pairs and nonadjacent pairs, and together they
partition the ten two-element subsets of Fin 5.

These are small kernel-checked finite combinatorial statements.
The automorphisms are the genuine graph automorphisms proved in
CycleFiveTransitivity, so EPPA makes multiplicities of outside
profiles constant on these orbits without coherent lifts.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Forward translates of one finite subset under all C5 rotations. -/
def cycleFiveSubsetOrbit (S : Finset (Fin 5)) :
    Finset (Finset (Fin 5)) :=
  (Finset.univ : Finset (Fin 5)).image
    (fun d => S.image (Equiv.addRight d))

/-- Representatives for the edge-pair and diagonal-pair orbits. -/
def cycleFiveEdgePair : Finset (Fin 5) := {0,1}
def cycleFiveDiagonalPair : Finset (Fin 5) := {0,2}

/-- Every two-subset has a five-element cyclic orbit. -/
theorem cycleFive_pair_orbit_size :
    ∀ S : Finset (Fin 5), S.card = 2 →
      (cycleFiveSubsetOrbit S).card = 5 := by
  decide

theorem cycleFive_edge_pair_orbit_card :
    (cycleFiveSubsetOrbit cycleFiveEdgePair).card = 5 := by
  decide

theorem cycleFive_diagonal_pair_orbit_card :
    (cycleFiveSubsetOrbit cycleFiveDiagonalPair).card = 5 := by
  decide

theorem cycleFive_pair_orbits_disjoint :
    Disjoint (cycleFiveSubsetOrbit cycleFiveEdgePair)
      (cycleFiveSubsetOrbit cycleFiveDiagonalPair) := by
  decide

/-- The two five-element orbits exhaust all ten unordered pairs. -/
theorem cycleFive_pair_orbits_partition :
    ((Finset.univ : Finset (Fin 5)).powersetCard 2) =
      cycleFiveSubsetOrbit cycleFiveEdgePair ∪
        cycleFiveSubsetOrbit cycleFiveDiagonalPair := by
  decide

/-- Outside-profile multiplicity is unchanged by every rotation
of the designated five-cycle in an actual EPPA witness. -/
theorem cycleFive_outside_profile_multiplicity_invariant
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (S : Finset (Fin 5)) (d : Fin 5) :
    outsideProfileMultiplicity H e (S.image (Equiv.addRight d)) =
      outsideProfileMultiplicity H e S := by
  exact (outside_profile_multiplicity_base_automorphism
    (SimpleGraph.cycleGraph 5) H e heppa (Equiv.addRight d)
    (cycleFive_translate_graph_automorphism d) S).symm

end EPPAIII.BlockSystems
