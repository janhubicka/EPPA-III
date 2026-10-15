import EPPAIII.BlockSystems.UniformCrossBlockDegrees
import EPPAIII.BlockSystems.Claim314CrossEdges

/-!
# Unit cross-degree gives a genuine perfect matching

For any vertex u and block b different from block(u), a neighbour
count equal to one means precisely one host vertex in b is adjacent
to u. If the invariant host partition has exactly two blocks, all
cross-block edges are captured by these degree-one neighbour sets.
Thus the actual cross-block graph has exactly one neighbour at every
vertex: its edges form a perfect matching.

This elementary final deduction is independent of EPPA. In
Lemma 3.12, the hard part is proving the common degree r equals one.
-/

namespace EPPAIII.BlockSystems

/-- A count of one neighbour into b yields a unique neighbour
of u in that actual host block. -/
theorem unique_neighbour_in_block_of_degree_one {W B : Type*}
    [Fintype W] [DecidableEq W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (block : W → B) (u : W) (b : B)
    (hDegree : neighboursInBlock H block u b = 1) :
    ∃! v : W, block v = b ∧ H.Adj u v := by
  classical
  let S : Finset W :=
    (Finset.univ : Finset W).filter
      (fun v => block v = b ∧ H.Adj u v)
  have hCard : S.card = 1 := hDegree
  obtain ⟨v,hSingleton⟩ := Finset.card_eq_one.mp hCard
  have hv : v ∈ S := by
    rw [hSingleton]
    simp
  have hvInfo : block v = b ∧ H.Adj u v :=
    (Finset.mem_filter.mp hv).2
  refine ⟨v,hvInfo,?_⟩
  intro w hw
  have hwS : w ∈ S :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
  rw [hSingleton] at hwS
  simpa using hwS

/-- A two-block host with uniform cross-block neighbour degree one
has exactly one cross-block neighbour at each vertex. -/
theorem two_block_cross_graph_perfect_matching {W B : Type*}
    [Fintype W] [DecidableEq W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (block : W → B)
    (i j : B) (hij : i ≠ j)
    (hTwo : ∀ b : B, b = i ∨ b = j)
    (hDegree : ∀ u : W, ∀ b : B, block u ≠ b →
      neighboursInBlock H block u b = 1) :
    ∀ u : W, ∃! v : W, (crossBlockGraph H block).Adj u v := by
  intro u
  rcases hTwo (block u) with hi | hj
  · have huj : block u ≠ j := by
      rw [hi]
      exact hij
    obtain ⟨v,hv,hUnique⟩ :=
      unique_neighbour_in_block_of_degree_one
        H block u j (hDegree u j huj)
    refine ⟨v, ?_, ?_⟩
    · exact ⟨hv.2, by rw [hi,hv.1]; exact hij⟩
    · intro w hw
      have hwb : block w = j := by
        rcases hTwo (block w) with hwi | hwj
        · exact False.elim (hw.2 (hi.trans hwi.symm))
        · exact hwj
      exact hUnique w ⟨hwb,hw.1⟩
  · have hui : block u ≠ i := by
      rw [hj]
      exact hij.symm
    obtain ⟨v,hv,hUnique⟩ :=
      unique_neighbour_in_block_of_degree_one
        H block u i (hDegree u i hui)
    refine ⟨v, ?_, ?_⟩
    · exact ⟨hv.2, by rw [hj,hv.1]; exact hij.symm⟩
    · intro w hw
      have hwb : block w = i := by
        rcases hTwo (block w) with hwi | hwj
        · exact hwi
        · exact False.elim (hw.2 (hj.trans hwj.symm))
      exact hUnique w ⟨hwb,hw.1⟩

end EPPAIII.BlockSystems
