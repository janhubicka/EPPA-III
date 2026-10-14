import EPPAIII.BlockSystems.Basic
import EPPAIII.BlockSystems.ClusterObstructions

/-!
# Case 1 of unequal cliques: base components occupy distinct blocks

If a genuine EPPA embedding has some selected edge inside an
Aut(H)-invariant block, then *every* selected edge is internal.
If the base does not lie in one block, every selected nonedge is
external: otherwise two-point EPPA would force all pairs of
distinct base vertices into the same block.

Consequently the induced block equivalence on base vertices
is exactly adjacency-or-equality. In particular the selected graph
is a disjoint union of cliques, and distinct clique components
occupy distinct host blocks. No coherent extension action is used.

This is the missing base-component separation in Claim 3.13.
It does not prove that host blocks themselves induce cliques.
-/

namespace EPPAIII.BlockSystems

/-- One selected internal edge propagates, by two-point EPPA,
to every edge of the selected graph. -/
theorem eppa_base_edges_internal_of_one {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hOneEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y)) :
    ∀ x y : V, G.Adj x y → block (e x) = block (e y) := by
  obtain ⟨u,v,huv,hInternal⟩ := hOneEdge
  intro x y hxy
  exact (eppa_edges_uniform_blocks
    G H e heppa block hBlocks u v x y huv hxy).mp hInternal

/-- Under a nontrivial selected block partition, all selected
nonedges must join distinct invariant blocks as soon as some
selected edge stays within a block. -/
theorem eppa_base_nonedges_external_of_internal_edge {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hOneEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hNotWhole : ∃ a b : V, block (e a) ≠ block (e b))
    (x y : V) (hxy : x ≠ y) (hnxy : ¬ G.Adj x y) :
    block (e x) ≠ block (e y) := by
  intro hSame
  obtain ⟨a,b,hab⟩ := hNotWhole
  have hne : a ≠ b := by
    intro h
    exact hab (congrArg (fun z : V => block (e z)) h)
  by_cases hAdj : G.Adj a b
  · have hAllEdges := eppa_base_edges_internal_of_one
      G H e heppa block hBlocks hOneEdge
    exact hab (hAllEdges a b hAdj)
  · have hAllNonedges :=
      (eppa_nonedges_uniform_blocks G H e heppa
        block hBlocks x y a b hxy hne hnxy hAdj).mp hSame
    exact hab hAllNonedges

/-- The restriction of the invariant-block equivalence relation to
the selected copy is adjacency together with equality. -/
theorem eppa_base_same_block_iff_eq_or_adj {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hOneEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hNotWhole : ∃ a b : V, block (e a) ≠ block (e b))
    (x y : V) :
    block (e x) = block (e y) ↔ x = y ∨ G.Adj x y := by
  constructor
  · intro hSame
    by_cases hxy : x = y
    · exact Or.inl hxy
    · by_cases hAdj : G.Adj x y
      · exact Or.inr hAdj
      · exact False.elim
          ((eppa_base_nonedges_external_of_internal_edge
              G H e heppa block hBlocks hOneEdge hNotWhole
              x y hxy hAdj) hSame)
  · rintro (h | h)
    · rw [h]
    · exact eppa_base_edges_internal_of_one
        G H e heppa block hBlocks hOneEdge x y h

/-- In this case, the existence of an invariant block system and
actual EPPA already forces the base to be a disjoint union of cliques. -/
theorem eppa_base_cluster_of_internal_edge {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hOneEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hNotWhole : ∃ a b : V, block (e a) ≠ block (e b)) :
    IsClusterGraph G := by
  intro x y z hxy hyz hxz
  have hXY := (eppa_base_same_block_iff_eq_or_adj
    G H e heppa block hBlocks hOneEdge hNotWhole x y).mpr (Or.inr hxy)
  have hYZ := (eppa_base_same_block_iff_eq_or_adj
    G H e heppa block hBlocks hOneEdge hNotWhole y z).mpr (Or.inr hyz)
  rcases (eppa_base_same_block_iff_eq_or_adj
    G H e heppa block hBlocks hOneEdge hNotWhole x z).mp
      (hXY.trans hYZ) with hEq | hAdj
  · exact False.elim (hxz hEq)
  · exact hAdj

end EPPAIII.BlockSystems
