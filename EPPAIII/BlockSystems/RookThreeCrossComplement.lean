import EPPAIII.BlockSystems.RookThreeUniformCrossDegree

/-!
# Complementation of cross degrees in the R3 two-half model

A vertex in the outside half has nine potential neighbours in the
selected half. The graph complement exchanges its actual
cross-degree k with 9-k. This is independent of EPPA, regularity,
a block system, and all external graph classifications.

The base rook-graph complement additionally needs relabelling by
the explicit self-complementing rook index, handled separately.
-/

namespace EPPAIII.BlockSystems

/-- Complementing both layers changes the actual cross-neighbour
count from k to 9-k, with no graph-theoretic hypothesis. -/
theorem rook_cross_degree_complement_sum_nine
    (H : SimpleGraph (Bool × rookVertex))
    [DecidableRel H.Adj] (x : rookVertex) :
    rookOutsideCrossDegree Hᶜ x +
      rookOutsideCrossDegree H x = 9 := by
  classical
  have hOne (y : rookVertex) :
      (if Hᶜ.Adj (true,x) (false,y) then 1 else 0) +
      (if H.Adj (true,x) (false,y) then 1 else 0) =
      (1 : ℕ) := by
    have hNe : (true,x) ≠ (false,y) := by
      intro hh
      exact Bool.true_ne_false (congrArg Prod.fst hh)
    by_cases h : H.Adj (true,x) (false,y)
    · simp [SimpleGraph.compl_adj,hNe,h]
    · simp [SimpleGraph.compl_adj,hNe,h]
  unfold rookOutsideCrossDegree
  calc
    (∑ y : rookVertex, if Hᶜ.Adj (true,x) (false,y) then 1 else 0) +
        (∑ y : rookVertex, if H.Adj (true,x) (false,y) then 1 else 0) =
          ∑ y : rookVertex,
            ((if Hᶜ.Adj (true,x) (false,y) then 1 else 0) +
             (if H.Adj (true,x) (false,y) then 1 else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ _y : rookVertex, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro y _
          exact hOne y
    _ = 9 := by decide

end EPPAIII.BlockSystems
