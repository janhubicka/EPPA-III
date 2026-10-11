import EPPAIII.CliqueCovers.RegularIndependentBound
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Independent sets occupy at most half a positive-degree regular graph

This specializes the symmetric-weighted matrix double-counting theorem
to the actual adjacency relation of a finite simple graph. A graph
with common positive degree d has no independent set larger than
half its vertices.

This is exactly the numerical inequality required of the true-twin
quotient in Lemma 3.7. The separate quotient construction and proof
of its vertex-transitivity remain further obligations.
-/

namespace EPPAIII.CliqueCovers

/-- A finite d-regular graph with d>0 has no independent set
containing more than half its vertices. -/
theorem regular_graph_independent_card_le_half {V : Type*}
    [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d)
    (hRegular : G.IsRegularOfDegree d)
    (S : Finset V) (hIndependent : G.IsIndepSet (S : Set V)) :
    2 * S.card ≤ Fintype.card V := by
  classical
  apply regular_symmetric_zero_block_le_half
    (fun u v : V => if G.Adj u v then (1 : ℕ) else 0)
    S d
  · intro u v
    by_cases h : G.Adj u v
    · simp [h, h.symm]
    · have hn : ¬ G.Adj v u := fun e => h e.symm
      simp [h, hn]
  · intro u
    calc
      (∑ v : V, if G.Adj u v then (1 : ℕ) else 0) =
          ((Finset.univ : Finset V).filter (fun v => G.Adj u v)).card := by
        simp
      _ = G.degree u := by
        simp [SimpleGraph.degree, G.neighborFinset_eq_filter]
      _ = d := hRegular u
  · intro u hu v hv
    have hNo : ¬ G.Adj u v := by
      by_cases huv : u = v
      · subst v
        exact G.irrefl _
      · exact hIndependent hu hv huv
    simp [hNo]
  · exact hd

end EPPAIII.CliqueCovers
