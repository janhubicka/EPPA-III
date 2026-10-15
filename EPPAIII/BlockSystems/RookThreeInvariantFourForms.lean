import EPPAIII.BlockSystems.RookThreePairTransitivity

/-!
# Four invariant graphs for the R3 rook action

The full 72-element rook automorphism subgroup has precisely two
orbits on unordered pairs of distinct vertices: edges and nonedges
of the rook graph.

Any graph invariant under that subgroup therefore has exactly two
Boolean adjacency parameters. Its four possibilities are the empty
graph, the rook graph, its complement, and the complete graph.

This is independent of EPPA. It will classify the complementary
nine-vertex induced graph after the outside profile map is used to
transport the genuine rook action from the selected copy.
-/

namespace EPPAIII.BlockSystems

/-- The adjacency relation of an invariant graph depends only on
whether the vertices are equal, rook-adjacent, or rook-nonadjacent. -/
theorem rook_invariant_graph_adj_characterization
    (K : SimpleGraph rookVertex)
    (hInvariant : ∀ p : rookAutParameter,
      IsGraphAutomorphism K (rookParameterizedAut p)) :
    ∀ u v : rookVertex,
      (K.Adj u v ↔ u ≠ v ∧
        (if rookThreeGraph.Adj u v then
          K.Adj (0,0) (0,1)
        else K.Adj (0,0) (1,1))) := by
  classical
  intro u v
  by_cases huv : u = v
  · subst v
    simp
  · by_cases hadj : rookThreeGraph.Adj u v
    · simpa [huv, hadj] using
        rook_invariant_graph_edge_value K hInvariant u v hadj
    · simpa [huv, hadj] using
        rook_invariant_graph_nonedge_value K hInvariant u v huv hadj

/-- Only four nine-vertex graphs are invariant under the full
rook-graph automorphism subgroup. -/
theorem rook_invariant_graph_four_forms
    (K : SimpleGraph rookVertex)
    (hInvariant : ∀ p : rookAutParameter,
      IsGraphAutomorphism K (rookParameterizedAut p)) :
    K = ⊥ ∨ K = rookThreeGraph ∨
      K = rookThreeGraphᶜ ∨ K = ⊤ := by
  classical
  have hAdj := rook_invariant_graph_adj_characterization K hInvariant
  by_cases hE : K.Adj (0,0) (0,1)
  · by_cases hN : K.Adj (0,0) (1,1)
    · right; right; right
      apply SimpleGraph.ext
      funext u v
      apply propext
      change K.Adj u v ↔ u ≠ v
      simpa [hE,hN] using hAdj u v
    · right; left
      apply SimpleGraph.ext
      funext u v
      apply propext
      change K.Adj u v ↔ rookThreeGraph.Adj u v
      have h := hAdj u v
      by_cases hadj : rookThreeGraph.Adj u v
      · have hne : u ≠ v := rookThreeGraph.ne_of_adj hadj
        simpa [hE,hN,hadj,hne] using h
      · simpa [hE,hN,hadj] using h
  · by_cases hN : K.Adj (0,0) (1,1)
    · right; right; left
      apply SimpleGraph.ext
      funext u v
      apply propext
      simpa [SimpleGraph.compl_adj,hE,hN] using hAdj u v
    · left
      apply SimpleGraph.ext
      funext u v
      apply propext
      change K.Adj u v ↔ False
      simpa [hE,hN] using hAdj u v

end EPPAIII.BlockSystems
