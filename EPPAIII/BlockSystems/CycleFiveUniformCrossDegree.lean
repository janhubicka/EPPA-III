import EPPAIII.BlockSystems.CycleFiveEmptyFullConclusion
import EPPAIII.CliqueCovers.RegularHalfEdges

/-!
# Uniform cross-degree of a transitive two-half C5 host

If both halves of a vertex-transitive ten-vertex graph induce
five-cycles, their internal degrees are two. Hence the cross-degree
of every vertex in the outside half equals the common host degree
minus two. This elementary proof avoids an assumed outside group
action or any coherent EPPA lifts.

It is the C5 counterpart of the already verified rook
regular-half cross-degree lemma.
-/

namespace EPPAIII.BlockSystems

def cycleFiveOutsideCrossDegree
    (H : SimpleGraph (Bool × Fin 5)) [DecidableRel H.Adj]
    (x : Fin 5) : ℕ :=
  ∑ y : Fin 5, if H.Adj (true,x) (false,y) then 1 else 0

theorem cycleFive_internal_row_sum_two :
    ∀ x : Fin 5,
      (∑ y : Fin 5,
        if (SimpleGraph.cycleGraph 5).Adj x y then 1 else 0) = 2 := by
  decide

/-- Both induced halves are five-cycles, so the outside
cross-degree is constant and between zero and five. -/
theorem cycleFive_paired_outside_uniform_cross_degree
    (H : SimpleGraph (Bool × Fin 5)) [DecidableRel H.Adj]
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTop : CliqueCovers.sideGraph H true =
      SimpleGraph.cycleGraph 5) :
    ∃ k : ℕ, k ≤ 5 ∧
      ∀ x : Fin 5, cycleFiveOutsideCrossDegree H x = k := by
  classical
  obtain ⟨D,hReg⟩ :=
    CliqueCovers.regular_of_transitive_graph H hTrans
  have hInsideTwo (x : Fin 5) :
      (∑ y : Fin 5,
        if H.Adj (true,x) (true,y) then 1 else 0) = 2 := by
    have hAdj (y : Fin 5) :
        H.Adj (true,x) (true,y) ↔
          (SimpleGraph.cycleGraph 5).Adj x y := by
      change (CliqueCovers.sideGraph H true).Adj x y ↔
        (SimpleGraph.cycleGraph 5).Adj x y
      rw [hTop]
    calc
      _ = ∑ y : Fin 5,
          if (SimpleGraph.cycleGraph 5).Adj x y then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [hAdj y]
      _ = 2 := cycleFive_internal_row_sum_two x
  have hCross (x : Fin 5) :
      cycleFiveOutsideCrossDegree H x + 2 = D := by
    have hDeg := hReg (true,x)
    have hSplit := CliqueCovers.sideDegree_eq_two_row_sums H true x
    have hWithin := hInsideTwo x
    unfold cycleFiveOutsideCrossDegree
    omega
  refine ⟨D - 2,?_,?_⟩
  · have hBound :
        cycleFiveOutsideCrossDegree H 0 ≤ 5 := by
      unfold cycleFiveOutsideCrossDegree
      calc
        (∑ y : Fin 5,
          if H.Adj (true,0) (false,y) then 1 else 0) ≤
          ∑ _y : Fin 5, (1 : ℕ) := by
            apply Finset.sum_le_sum
            intro y _
            split <;> omega
        _ = 5 := by decide
    have hh := hCross 0
    omega
  · intro x
    have hh := hCross x
    omega

end EPPAIII.BlockSystems
