import EPPAIII.BlockSystems.RookThreePairTransitivity
import EPPAIII.BlockSystems.TransitivePartition
import EPPAIII.EPPA.ProfileAction

/-!
# Primitivity of the actual nine-vertex rook action

A relation invariant under the explicit row/column-permutation and
transpose subgroup is either equality or the universal relation,
provided it is an equivalence relation. In particular the relation
"two selected vertices lie in the same actual host imprimitivity
block" has these two possibilities.

The proof uses the verified transitivity on oriented rook edges and
nonedges, and a small finite diameter-two certificate for each
of the rook graph and its complement. This closes the mathematical
gap between the rooted stabilizer computation and arbitrary
EPPA-invariant equivalence relations on the selected vertices.
-/

namespace EPPAIII.BlockSystems

/-- Two nonadjacent rook vertices have a common rook neighbour. -/
theorem rook_nonedge_has_common_neighbour :
    ∀ u v : rookVertex, u ≠ v → ¬ rookThreeGraph.Adj u v →
      ∃ w : rookVertex,
        rookThreeGraph.Adj u w ∧ rookThreeGraph.Adj w v := by
  decide

/-- Two adjacent rook vertices have a common *non*-neighbour
distinct from both endpoints. -/
theorem rook_edge_has_common_nonneighbour :
    ∀ u v : rookVertex, rookThreeGraph.Adj u v →
      ∃ w : rookVertex,
        (u ≠ w ∧ ¬ rookThreeGraph.Adj u w) ∧
        (w ≠ v ∧ ¬ rookThreeGraph.Adj w v) := by
  decide

/-- The 72 indexed genuine rook automorphisms act primitively
on nine points: there are no nontrivial invariant equivalence
relations. No graph-classification theorem is used. -/
theorem rook_invariant_equivalence_trivial
    {B : Type*} (b : rookVertex → B)
    (hInvariant : ∀ p : rookAutParameter, ∀ x y : rookVertex,
      b x = b y ↔
        b (rookParameterizedAut p x) = b (rookParameterizedAut p y)) :
    Function.Injective b ∨ ∀ x y : rookVertex, b x = b y := by
  classical
  by_cases hInj : Function.Injective b
  · exact Or.inl hInj
  right
  have hPair : ∃ u v : rookVertex, u ≠ v ∧ b u = b v := by
    by_contra hNo
    apply hInj
    intro u v huv
    by_contra hne
    exact hNo ⟨u,v,hne,huv⟩
  obtain ⟨u₀,v₀,huv,hSame⟩ := hPair
  by_cases hAdj : rookThreeGraph.Adj u₀ v₀
  · obtain ⟨p₀,hpU,hpV⟩ :=
      rook_ordered_edge_pair_transitive u₀ v₀ hAdj
    have hCanon : b (0,0) = b (0,1) :=
      (hInvariant p₀ (0,0) (0,1)).mpr (by
        simpa only [hpU,hpV] using hSame)
    have hAllEdges (u v : rookVertex)
        (huv : rookThreeGraph.Adj u v) : b u = b v := by
      obtain ⟨p,hpU,hpV⟩ :=
        rook_ordered_edge_pair_transitive u v huv
      have h := (hInvariant p (0,0) (0,1)).mp hCanon
      simpa only [hpU,hpV] using h
    intro u v
    by_cases hEq : u = v
    · exact congrArg b hEq
    by_cases hUV : rookThreeGraph.Adj u v
    · exact hAllEdges u v hUV
    obtain ⟨w,hu,hw⟩ :=
      rook_nonedge_has_common_neighbour u v hEq hUV
    exact (hAllEdges u w hu).trans (hAllEdges w v hw)
  · obtain ⟨p₀,hpU,hpV⟩ :=
      rook_ordered_nonedge_pair_transitive u₀ v₀ huv hAdj
    have hCanon : b (0,0) = b (1,1) :=
      (hInvariant p₀ (0,0) (1,1)).mpr (by
        simpa only [hpU,hpV] using hSame)
    have hAllNonedges (u v : rookVertex)
        (hne : u ≠ v) (hnadj : ¬ rookThreeGraph.Adj u v) :
        b u = b v := by
      obtain ⟨p,hpU,hpV⟩ :=
        rook_ordered_nonedge_pair_transitive u v hne hnadj
      have h := (hInvariant p (0,0) (1,1)).mp hCanon
      simpa only [hpU,hpV] using h
    intro u v
    by_cases hEq : u = v
    · exact congrArg b hEq
    by_cases hUV : rookThreeGraph.Adj u v
    · obtain ⟨w,⟨huw,hNonUW⟩,⟨hwv,hNonWV⟩⟩ :=
        rook_edge_has_common_nonneighbour u v hUV
      exact (hAllNonedges u w huw hNonUW).trans
        (hAllNonedges w v hwv hNonWV)
    · exact hAllNonedges u v hEq hUV

/-- In an actual EPPA host with invariant blocks, the selected
rook vertices are either a transversal of the blocks or all
lie in one block. This derives invariance from full EPPA lifts,
without requiring coherent choices of those lifts. -/
theorem rook_eppa_selected_block_transversal_or_single
    {W B : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block) :
    Function.Injective (fun x : rookVertex => block (e x)) ∨
      ∀ x y : rookVertex, block (e x) = block (e y) := by
  apply rook_invariant_equivalence_trivial
  intro p x y
  obtain ⟨q,hq,hCompat⟩ :=
    eppa_lifts_total rookThreeGraph H e heppa
      (rookParameterizedAut p)
      (rookParameterizedAut_graph_automorphism p)
  have hPreserve := hBlocks q hq (e x) (e y)
  simpa only [hCompat x,hCompat y] using hPreserve

end EPPAIII.BlockSystems
