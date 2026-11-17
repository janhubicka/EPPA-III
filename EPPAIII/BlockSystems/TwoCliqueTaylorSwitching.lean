import EPPAIII.BlockSystems.TwoCliqueSwitching
import EPPAIII.TwoGraphs.TransversalParity

/-!
# The switching-class conclusion of unequal-clique Lemma 6.6

The existing two-clique theorem uses `seidelSwitchGraph`, whereas
Section 5 defines switching-class representatives as Taylor transversals.
This file verifies directly that these two constructions agree, and
then records the full source-facing consequence: every two-clique
partition (including a single complete clique) belongs to the
switching class of every other two-clique partition.

The proof makes no EPPA, transitivity, imprimitivity, or homogeneous-
graph classification assumptions. Those belong to the separate
host-classification portion of Lemma 6.6.
-/

namespace EPPAIII.BlockSystems

/-- Seidel switching and the induced Taylor transversal are precisely
the same graph on the same labelled vertex set, including the diagonal. -/
theorem seidelSwitchGraph_eq_taylorTransversalGraph
    {V : Type*} (G : SimpleGraph V) (mask : V → Bool) :
    seidelSwitchGraph G mask =
      EPPAIII.TwoGraphs.taylorTransversalGraph G mask := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  change (u ≠ v ∧
      (if mask u = mask v then G.Adj u v else ¬ G.Adj u v)) ↔
    (u ≠ v ∧ (G.Adj u v ↔ mask u = mask v))
  by_cases hMask : mask u = mask v
  · simp [hMask]
  · simp [hMask]

/-- Any two Boolean partitions into cliques are representatives
of the same Taylor-transversal switching class. -/
theorem twoCliqueGraph_taylorTransversal_to_any_twoClique
    {V : Type*} (c d : V → Bool) :
    EPPAIII.TwoGraphs.taylorTransversalGraph (twoCliqueGraph c)
      (fun v => Bool.xor (c v) (d v)) =
        twoCliqueGraph d := by
  calc
    EPPAIII.TwoGraphs.taylorTransversalGraph (twoCliqueGraph c)
        (fun v => Bool.xor (c v) (d v)) =
      seidelSwitchGraph (twoCliqueGraph c)
        (fun v => Bool.xor (c v) (d v)) :=
      (seidelSwitchGraph_eq_taylorTransversalGraph _ _).symm
    _ = twoCliqueGraph d :=
      twoCliqueGraph_switch_to_any_twoClique c d

/-- In particular the complete graph is a representative of the
switching class of any graph that is the union of two cliques. -/
theorem twoCliqueGraph_taylorTransversal_to_complete
    {V : Type*} (c : V → Bool) :
    EPPAIII.TwoGraphs.taylorTransversalGraph (twoCliqueGraph c) c =
      (⊤ : SimpleGraph V) := by
  calc
    EPPAIII.TwoGraphs.taylorTransversalGraph (twoCliqueGraph c) c =
      seidelSwitchGraph (twoCliqueGraph c) c :=
      (seidelSwitchGraph_eq_taylorTransversalGraph _ _).symm
    _ = (⊤ : SimpleGraph V) := twoCliqueGraph_switch_to_complete c

end EPPAIII.BlockSystems
