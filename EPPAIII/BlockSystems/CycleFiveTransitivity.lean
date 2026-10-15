import EPPAIII.CliqueCovers.TransitiveHalfEdges
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# The canonical five-cycle is vertex-transitive

This is the concrete group-action input for the exceptional C5
case of Lemma 3.18. We use translation in the additive group
Fin 5. Translation preserves the circulant adjacency relation
and takes any chosen vertex to any other vertex.
-/

namespace EPPAIII.BlockSystems

/-- Translation by d is a graph automorphism of C5. -/
theorem cycleFive_translate_graph_automorphism (d : Fin 5) :
    IsGraphAutomorphism (SimpleGraph.cycleGraph 5)
      (Equiv.addRight d) := by
  intro u v
  change (SimpleGraph.cycleGraph 5).Adj u v ↔
    (SimpleGraph.cycleGraph 5).Adj (u + d) (v + d)
  rw [show (5 : ℕ) = 4 + 1 by omega,
    SimpleGraph.cycleGraph_eq_circulantGraph]
  exact (SimpleGraph.circulantGraph_adj_translate
    (s := ({1} : Set (Fin 5))) (u := u) (v := v) (d := d)).symm

/-- The canonical C5 is vertex-transitive, without appealing
to any finite graph classification. -/
theorem cycleFive_vertex_transitive :
    CliqueCovers.HasTransitiveGraphAutomorphisms
      (SimpleGraph.cycleGraph 5) := by
  intro u v
  let d : Fin 5 := v - u
  let q : Equiv.Perm (Fin 5) := Equiv.addRight d
  refine ⟨q,cycleFive_translate_graph_automorphism d,?_⟩
  change u + (v - u) = v
  abel

end EPPAIII.BlockSystems
