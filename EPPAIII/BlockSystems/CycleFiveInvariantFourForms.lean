import EPPAIII.BlockSystems.CycleFiveTransitivity

/-!
# The four graphs invariant under cyclic translation on five vertices

Cyclic translations of Fin 5 are genuine automorphisms of C5.
They have precisely two orbits on unordered pairs: consecutive
vertices and diagonal pairs. Because graph adjacency is symmetric,
translations plus the symmetry of any simple graph are sufficient
to force two independent Boolean adjacency bits.

Thus every graph on Fin 5 invariant under all cyclic translations
is the empty graph, C5, its complement, or the complete graph.
This lemma does not use EPPA; it will classify the induced outside
half after its pair profiles are canonically labelled.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192

/-- Cyclic translates, allowing reversal, cover all oriented edges
of the canonical C5. -/
theorem cycleFive_edge_oriented_pair_action :
    ∀ u v : Fin 5, (SimpleGraph.cycleGraph 5).Adj u v →
      ∃ d : Fin 5,
        (u = (0 : Fin 5) + d ∧ v = (1 : Fin 5) + d) ∨
        (u = (1 : Fin 5) + d ∧ v = (0 : Fin 5) + d) := by
  decide

/-- Cyclic translates, allowing reversal, also cover all oriented
nonedges between distinct C5 vertices. -/
theorem cycleFive_diagonal_oriented_pair_action :
    ∀ u v : Fin 5, u ≠ v →
      ¬ (SimpleGraph.cycleGraph 5).Adj u v →
      ∃ d : Fin 5,
        (u = (0 : Fin 5) + d ∧ v = (2 : Fin 5) + d) ∨
        (u = (2 : Fin 5) + d ∧ v = (0 : Fin 5) + d) := by
  decide

/-- An invariant graph has constant adjacency on C5 edges. -/
theorem cycleFive_invariant_graph_edge_value
    (K : SimpleGraph (Fin 5))
    (hInv : ∀ d : Fin 5,
      IsGraphAutomorphism K (Equiv.addRight d))
    (u v : Fin 5) (hAdj : (SimpleGraph.cycleGraph 5).Adj u v) :
    K.Adj u v ↔ K.Adj 0 1 := by
  obtain ⟨d,h⟩ := cycleFive_edge_oriented_pair_action u v hAdj
  rcases h with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]
    exact (hInv d 0 1).symm
  · rw [hu,hv]
    exact (K.adj_comm _ _).trans (hInv d 0 1).symm

/-- An invariant graph has constant adjacency on C5 diagonals. -/
theorem cycleFive_invariant_graph_diagonal_value
    (K : SimpleGraph (Fin 5))
    (hInv : ∀ d : Fin 5,
      IsGraphAutomorphism K (Equiv.addRight d))
    (u v : Fin 5) (hne : u ≠ v)
    (hnAdj : ¬ (SimpleGraph.cycleGraph 5).Adj u v) :
    K.Adj u v ↔ K.Adj 0 2 := by
  obtain ⟨d,h⟩ := cycleFive_diagonal_oriented_pair_action u v hne hnAdj
  rcases h with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]
    exact (hInv d 0 2).symm
  · rw [hu,hv]
    exact (K.adj_comm _ _).trans (hInv d 0 2).symm

/-- Every five-vertex simple graph invariant under the cyclic
rotation of the five-cycle is one of the four elementary forms. -/
theorem cycleFive_invariant_graph_four_forms
    (K : SimpleGraph (Fin 5))
    (hInv : ∀ d : Fin 5,
      IsGraphAutomorphism K (Equiv.addRight d)) :
    K = ⊥ ∨ K = SimpleGraph.cycleGraph 5 ∨
      K = (SimpleGraph.cycleGraph 5)ᶜ ∨ K = ⊤ := by
  classical
  have hAdj (u v : Fin 5) :
      K.Adj u v ↔ u ≠ v ∧
        (if (SimpleGraph.cycleGraph 5).Adj u v then
          K.Adj 0 1 else K.Adj 0 2) := by
    by_cases hne : u = v
    · subst v
      simp
    · by_cases hE : (SimpleGraph.cycleGraph 5).Adj u v
      · simpa [hne,hE] using
          cycleFive_invariant_graph_edge_value K hInv u v hE
      · simpa [hne,hE] using
          cycleFive_invariant_graph_diagonal_value K hInv u v hne hE
  by_cases hE : K.Adj 0 1
  · by_cases hD : K.Adj 0 2
    · right; right; right
      apply SimpleGraph.ext
      funext u v
      apply propext
      change K.Adj u v ↔ u ≠ v
      simpa [hE,hD] using hAdj u v
    · right; left
      apply SimpleGraph.ext
      funext u v
      apply propext
      have h := hAdj u v
      by_cases hEdge : (SimpleGraph.cycleGraph 5).Adj u v
      · have hne : u ≠ v := (SimpleGraph.cycleGraph 5).ne_of_adj hEdge
        simpa [hne,hE,hD,hEdge] using h
      · simpa [hE,hD,hEdge] using h
  · by_cases hD : K.Adj 0 2
    · right; right; left
      apply SimpleGraph.ext
      funext u v
      apply propext
      simpa [SimpleGraph.compl_adj,hE,hD] using hAdj u v
    · left
      apply SimpleGraph.ext
      funext u v
      apply propext
      change K.Adj u v ↔ False
      simpa [hE,hD] using hAdj u v

end EPPAIII.BlockSystems
