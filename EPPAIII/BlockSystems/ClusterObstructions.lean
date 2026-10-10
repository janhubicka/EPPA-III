import EPPAIII.BlockSystems.Transversal

/-!
# Cluster graphs and the P3 obstruction

A graph is a disjoint union of cliques exactly when adjacency,
augmented by equality, is transitive. Its failure is an induced
three-vertex path. The complemented statement gives the second
induced triple used in Claim 3.4.

These predicates avoid depending on a particular choice of
disjoint-clique decomposition in the Lean theorem.
-/

namespace EPPAIII.BlockSystems

/-- Transitivity of adjacency among three distinct vertices.
Equivalently, G is a disjoint union of cliques. -/
def IsClusterGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V,
    G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c

/-- Transitivity of the nonadjacency relation on distinct vertices.
Equivalently, the complement of G is a disjoint union of cliques. -/
def IsCoClusterGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V,
    a ≠ b → b ≠ c → a ≠ c →
    ¬ G.Adj a b → ¬ G.Adj b c → ¬ G.Adj a c

/-- Not being a disjoint union of cliques is exactly the existence
of an induced three-vertex path. -/
theorem not_cluster_iff_induced_p3 {V : Type*}
    (G : SimpleGraph V) :
    ¬ IsClusterGraph G ↔ HasInducedP3 G := by
  classical
  constructor
  · intro h
    by_contra hNo
    apply h
    intro a b c hab hbc hac
    by_contra hnac
    apply hNo
    exact ⟨a, b, c, G.ne_of_adj hab, G.ne_of_adj hbc,
      hac, hab, hbc, hnac⟩
  · rintro ⟨a,b,c,_,_,hac,hab,hbc,hnac⟩ hCluster
    exact hnac (hCluster a b c hab hbc hac)

/-- The same characterization after complementing edges. -/
theorem not_cocluster_iff_induced_cop3 {V : Type*}
    (G : SimpleGraph V) :
    ¬ IsCoClusterGraph G ↔ HasInducedCoP3 G := by
  classical
  constructor
  · intro h
    by_contra hNo
    apply h
    intro a b c habNe hbcNe hacNe hnab hnbc
    by_contra hAdj
    apply hNo
    exact ⟨a,b,c,habNe,hbcNe,hacNe,hnab,hnbc,hAdj⟩
  · rintro ⟨a,b,c,habNe,hbcNe,hacNe,hnab,hnbc,hac⟩ hCoCluster
    exact (hCoCluster a b c habNe hbcNe hacNe hnab hnbc) hac

/-- A convenient theorem interface matching the manuscript exclusions:
neither G nor its complement is a union of cliques. -/
theorem transversal_of_noncluster {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hNonCluster : ¬ IsClusterGraph G)
    (hNonCoCluster : ¬ IsCoClusterGraph G)
    (hNotWhole : ∃ u v : V, block (e u) ≠ block (e v)) :
    Function.Injective (fun x : V => block (e x)) := by
  exact selected_vertices_transversal G H e heppa block hBlocks
    ((not_cluster_iff_induced_p3 G).mp hNonCluster)
    ((not_cocluster_iff_induced_cop3 G).mp hNonCoCluster)
    hNotWhole

end EPPAIII.BlockSystems
