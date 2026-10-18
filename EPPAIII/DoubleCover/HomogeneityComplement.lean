import EPPAIII.EPPA.ComplementTransport
import EPPAIII.DoubleCover.RigidLayerHomogeneity

/-!
# Homogeneity and complementing the graph

This isolates the logical complement-transfer step from the imprimitive
classification. The same partial permutations and total permutations
preserve a graph and its complement. Thus homogeneity, unlike being a
cluster graph, is invariant under complementation.

This does *not* assert that every vertex-transitive cluster graph is
homogeneous: that elementary bridge is recorded separately for
author review.
-/

namespace EPPAIII.DoubleCover

/-- Graph homogeneity is invariant under complementation, for any
vertex type; no cardinality or transitivity assumptions are needed. -/
theorem homogeneous_complement_iff {V : Type*}
    (G : SimpleGraph V) :
    IsHomogeneousGraph G ↔ IsHomogeneousGraph Gᶜ := by
  constructor
  · intro h D p hp
    obtain ⟨q, hq, hfix⟩ :=
      h D p (EPPAIII.partial_complement_implies_original G D p hp)
    exact ⟨q, EPPAIII.BlockSystems.graphAutomorphism_complement G q hq, hfix⟩
  · intro h D p hp
    obtain ⟨q, hq, hfix⟩ :=
      h D p (EPPAIII.partial_original_implies_complement G D p hp)
    refine ⟨q, ?_, hfix⟩
    have hq' :=
      EPPAIII.BlockSystems.graphAutomorphism_complement Gᶜ q hq
    simpa using hq'

/-- The negation of graph homogeneity is also complement-invariant. -/
theorem nonhomogeneous_complement_iff {V : Type*}
    (G : SimpleGraph V) :
    ¬ IsHomogeneousGraph G ↔ ¬ IsHomogeneousGraph Gᶜ := by
  constructor
  · intro h hc
    exact h ((homogeneous_complement_iff G).mpr hc)
  · intro h hc
    exact h ((homogeneous_complement_iff G).mp hc)

end EPPAIII.DoubleCover
