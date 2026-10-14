import EPPAIII.BlockSystems.SharedCrossNeighbours
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Shared neighbours connect an entire bipartite piece

Suppose S,T are finite vertex sets. If every two distinct
vertices of S have a common neighbour in J, and every
vertex of T has a neighbour in S, all vertices in S∪T
are reachable from one another in J.

This is the short connectivity argument underlying the
unequal-clique Case-1 matching reduction. The actual
two-point EPPA theorem forces the shared-neighbour
property once the cross-block degree r is at least two.
-/

namespace EPPAIII.BlockSystems

/-- A common neighbour yields a walk of length two between
the two given vertices. -/
theorem reachable_of_common_neighbour {W : Type*}
    (J : SimpleGraph W) (u v : W)
    (hCommon : HasCommonNeighbour J u v) :
    J.Reachable u v := by
  obtain ⟨w,huw,hvw⟩ := hCommon
  exact huw.reachable.trans hvw.symm.reachable

/-- If all distinct vertices in a finite set S share a
neighbour, S is internally reachable. -/
theorem reachable_of_shared_pairs {W : Type*}
    (J : SimpleGraph W) (S : Finset W)
    (hShared : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      HasCommonNeighbour J u v)
    (u v : W) (hu : u ∈ S) (hv : v ∈ S) :
    J.Reachable u v := by
  by_cases hEq : u = v
  · subst v
    exact SimpleGraph.Reachable.refl u
  · exact reachable_of_common_neighbour J u v
      (hShared u hu v hv hEq)

/-- The union S∪T is internally connected if S has shared
neighbours for every distinct pair and every T-vertex
has at least one S-neighbour. -/
theorem shared_pairs_connected_union {W : Type*}
    (J : SimpleGraph W) (S T : Finset W)
    (hShared : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      HasCommonNeighbour J u v)
    (hTouches : ∀ v ∈ T, ∃ u ∈ S, J.Adj v u) :
    ∀ x ∈ S ∪ T, ∀ y ∈ S ∪ T, J.Reachable x y := by
  have hConnectToS (w : W) (hw : w ∈ S ∪ T) :
      ∃ u ∈ S, J.Reachable w u := by
    rcases Finset.mem_union.mp hw with hwS | hwT
    · exact ⟨w,hwS,SimpleGraph.Reachable.refl w⟩
    · obtain ⟨u,hu,hwu⟩ := hTouches w hwT
      exact ⟨u,hu,hwu.reachable⟩
  intro x hx y hy
  obtain ⟨a,ha,hxa⟩ := hConnectToS x hx
  obtain ⟨b,hb,hyb⟩ := hConnectToS y hy
  have hab : J.Reachable a b :=
    reachable_of_shared_pairs J S hShared a b ha hb
  exact hxa.trans (hab.trans hyb.symm)

end EPPAIII.BlockSystems
