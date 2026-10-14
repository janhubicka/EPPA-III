import EPPAIII.BlockSystems.TransitiveComponentSizes

/-!
# Closed internally connected vertex sets are full components

If S is closed under adjacency and its vertices are mutually
reachable, it is precisely one complete connected component
of the host graph. Two disjoint nonempty such sets in a
vertex-transitive finite graph must have the same cardinality,
by the component-size invariance theorem.

This finite graph lemma is tailored to the two unequal
bipartite cross-edge pieces arising when r>=2 in the
Case-1 perfect-matching proof.
-/

namespace EPPAIII.BlockSystems

/-- Reachability preserves every vertex predicate closed under
following graph edges. The proof uses finite reflexive-transitive
closure directly, without adding a path-existence assumption. -/
theorem reachable_mem_of_adj_closed {W : Type*}
    (J : SimpleGraph W) (S : Set W)
    (hClosed : ∀ u ∈ S, ∀ v : W, J.Adj u v → v ∈ S)
    (u v : W) (hu : u ∈ S) (hReach : J.Reachable u v) :
    v ∈ S := by
  have hr : Relation.ReflTransGen J.Adj u v :=
    (J.reachable_iff_reflTransGen u v).mp hReach
  clear hReach
  induction hr with
  | refl => exact hu
  | tail _ hadj ih => exact hClosed _ ih _ hadj

/-- A nonempty edge-closed set internally connected by graph
walks is exactly the connected component of any of its vertices. -/
theorem reachableVertices_eq_of_closed_connected {W : Type*}
    [Fintype W]
    (J : SimpleGraph W) (S : Finset W) (u : W)
    (hu : u ∈ S)
    (hClosed : ∀ a ∈ S, ∀ b : W, J.Adj a b → b ∈ S)
    (hConnected : ∀ v ∈ S, J.Reachable u v) :
    reachableVertices J u = S := by
  classical
  ext v
  simp only [reachableVertices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hReach
    exact reachable_mem_of_adj_closed J (S : Set W)
      hClosed u v hu hReach
  · exact hConnected v

/-- Two nonempty internally connected vertex sets that are
both closed under graph adjacency have equal sizes in any
finite vertex-transitive graph. -/
theorem transitive_closed_connected_sets_card_eq {W : Type*}
    [Fintype W]
    (J : SimpleGraph W)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms J)
    (S T : Finset W)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hClosedS : ∀ a ∈ S, ∀ b : W, J.Adj a b → b ∈ S)
    (hClosedT : ∀ a ∈ T, ∀ b : W, J.Adj a b → b ∈ T)
    (hConnectedS : ∀ a ∈ S, ∀ b ∈ S, J.Reachable a b)
    (hConnectedT : ∀ a ∈ T, ∀ b ∈ T, J.Reachable a b) :
    S.card = T.card := by
  classical
  obtain ⟨s,hs⟩ := hS
  obtain ⟨t,ht⟩ := hT
  have hCompS := reachableVertices_eq_of_closed_connected
    J S s hs hClosedS (hConnectedS s hs)
  have hCompT := reachableVertices_eq_of_closed_connected
    J T t ht hClosedT (hConnectedT t ht)
  calc
    S.card = (reachableVertices J s).card :=
      (congrArg Finset.card hCompS).symm
    _ = (reachableVertices J t).card :=
      transitive_connected_component_card_eq J hTrans s t
    _ = T.card := congrArg Finset.card hCompT

end EPPAIII.BlockSystems
