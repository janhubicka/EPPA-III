import EPPAIII.BlockSystems.Basic

/-!
# Claim 3.4: the selected graph is a transversal of the blocks

The manuscript excludes graphs which are disjoint unions of cliques or
their complements. Equivalently, the base contains an induced P3 and
an induced complement of P3. The two induced triples force the images
of any two *distinct* selected vertices to belong to different blocks,
unless all selected vertices belong to the same block.

This is the central non-counting step of Claim 3.4. The separate
"all of G in one block implies G homogeneous" step is not assumed by
the manuscript, and will be addressed independently.
-/

namespace EPPAIII.BlockSystems

/-- An induced path with three pairwise distinct vertices. -/
def HasInducedP3 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c : V,
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    G.Adj a b ∧ G.Adj b c ∧ ¬ G.Adj a c

/-- An induced complement of a three-vertex path. -/
def HasInducedCoP3 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c : V,
    a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    ¬ G.Adj a b ∧ ¬ G.Adj b c ∧ G.Adj a c

/-- If an edge of G lies within a block, then P3-freeness
would be necessary unless the entirety of G lies in one block. -/
theorem edges_cross_of_induced_p3 {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hp3 : HasInducedP3 G)
    (hNotWhole : ∃ u v : V, block (e u) ≠ block (e v)) :
    ∀ x y : V, G.Adj x y → block (e x) ≠ block (e y) := by
  intro x y hxy hSame
  obtain ⟨a,b,c,_,_,hac,hab,hbc,hnac⟩ := hp3
  have habSame : block (e a) = block (e b) :=
    (eppa_edges_uniform_blocks G H e heppa block hBlocks x y a b hxy hab).mp hSame
  have hbcSame : block (e b) = block (e c) :=
    (eppa_edges_uniform_blocks G H e heppa block hBlocks x y b c hxy hbc).mp hSame
  have hacSame : block (e a) = block (e c) := habSame.trans hbcSame
  obtain ⟨u,v,huv⟩ := hNotWhole
  by_cases hEq : u = v
  · subst v
    exact huv rfl
  by_cases hEdge : G.Adj u v
  · have huu :=
      (eppa_edges_uniform_blocks G H e heppa block hBlocks x y u v hxy hEdge).mp hSame
    exact huv huu
  · have huu :=
      (eppa_nonedges_uniform_blocks G H e heppa block hBlocks
        a c u v hac hEq hnac hEdge).mp hacSame
    exact huv huu

/-- The complementary induced path similarly excludes a base
nonedge inside a block, unless the whole base is one block. -/
theorem nonedges_cross_of_induced_cop3 {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hcop3 : HasInducedCoP3 G)
    (hNotWhole : ∃ u v : V, block (e u) ≠ block (e v)) :
    ∀ x y : V, x ≠ y → ¬ G.Adj x y →
      block (e x) ≠ block (e y) := by
  intro x y hxy hnxy hSame
  obtain ⟨a,b,c,habNe,hbcNe,hacNe,hnab,hnbc,hac⟩ := hcop3
  have habSame : block (e a) = block (e b) :=
    (eppa_nonedges_uniform_blocks G H e heppa block hBlocks
      x y a b hxy habNe hnxy hnab).mp hSame
  have hbcSame : block (e b) = block (e c) :=
    (eppa_nonedges_uniform_blocks G H e heppa block hBlocks
      x y b c hxy hbcNe hnxy hnbc).mp hSame
  have hacSame : block (e a) = block (e c) := habSame.trans hbcSame
  obtain ⟨u,v,huv⟩ := hNotWhole
  by_cases hEq : u = v
  · subst v
    exact huv rfl
  by_cases hEdge : G.Adj u v
  · have huu :=
      (eppa_edges_uniform_blocks G H e heppa block hBlocks
        a c u v hac hEdge).mp hacSame
    exact huv huu
  · have huu :=
      (eppa_nonedges_uniform_blocks G H e heppa block hBlocks
        x y u v hxy hEq hnxy hEdge).mp hSame
    exact huv huu

/-- Selected vertices occupy pairwise distinct blocks provided the
graph has both forbidden induced triples and is not contained
entirely in one block. -/
theorem selected_vertices_transversal {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hp3 : HasInducedP3 G) (hcop3 : HasInducedCoP3 G)
    (hNotWhole : ∃ u v : V, block (e u) ≠ block (e v)) :
    Function.Injective (fun x : V => block (e x)) := by
  intro x y hSame
  by_contra hxy
  by_cases hAdj : G.Adj x y
  · exact (edges_cross_of_induced_p3
      G H e heppa block hBlocks hp3 hNotWhole x y hAdj) hSame
  · exact (nonedges_cross_of_induced_cop3
      G H e heppa block hBlocks hcop3 hNotWhole x y hxy hAdj) hSame

end EPPAIII.BlockSystems
