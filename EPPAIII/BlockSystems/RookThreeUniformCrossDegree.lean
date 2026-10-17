import EPPAIII.BlockSystems.RookThreePairOutsideGraph

/-!
# Uniform R3 cross-degree from regularity of both halves

For a vertex-transitive graph H with each induced half 4-regular,
the number of cross-neighbours of any outside vertex is the
common host degree minus four. For R3 (or anti-R3) the inside
degree is four, so its external degree is uniform and ≤ 9.

The proof counts adjacency rows directly, so its finite counting
statements do not depend on an arbitrary DecidableRel instance
for graph degree and edge finsets.
-/

namespace EPPAIII.BlockSystems

/-- Number of cross neighbours of a vertex in the top half. -/
def rookOutsideCrossDegree
    (H : SimpleGraph (Bool × rookVertex))
    [DecidableRel H.Adj] (x : rookVertex) : ℕ :=
  ∑ y : rookVertex,
    if H.Adj (true,x) (false,y) then 1 else 0

/-- R3 and its complement both have exactly four neighbours,
written as finite Boolean sums. -/
theorem rook_four_internal_row_sums :
    (∀ x : rookVertex,
      (∑ y : rookVertex,
        if rookThreeGraph.Adj x y then 1 else 0) = 4) ∧
    (∀ x : rookVertex,
      (∑ y : rookVertex,
        if rookThreeGraphᶜ.Adj x y then 1 else 0) = 4) := by
  constructor <;> decide

/-- From full-host transitivity and an induced rook or anti-rook
outside half, all nine outside vertices have a common number
of cross neighbours, between zero and nine. -/
theorem rook_paired_outside_uniform_cross_degree
    (H : SimpleGraph (Bool × rookVertex))
    [DecidableRel H.Adj]
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTop : CliqueCovers.sideGraph H true = rookThreeGraph ∨
       CliqueCovers.sideGraph H true = rookThreeGraphᶜ) :
    ∃ k : ℕ, k ≤ 9 ∧
      ∀ x : rookVertex, rookOutsideCrossDegree H x = k := by
  classical
  obtain ⟨D,hReg⟩ :=
    CliqueCovers.regular_of_transitive_graph H hTrans
  have hInsideFour (x : rookVertex) :
      (∑ y : rookVertex,
        if H.Adj (true,x) (true,y) then 1 else 0) = 4 := by
    rcases hTop with hRook | hAnti
    · have hAdj (y : rookVertex) :
          H.Adj (true,x) (true,y) ↔ rookThreeGraph.Adj x y := by
        change (CliqueCovers.sideGraph H true).Adj x y ↔
          rookThreeGraph.Adj x y
        rw [hRook]
      calc
        _ = ∑ y : rookVertex,
            if rookThreeGraph.Adj x y then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro y _
              simp only [hAdj y]
        _ = 4 := rook_four_internal_row_sums.1 x
    · have hAdj (y : rookVertex) :
          H.Adj (true,x) (true,y) ↔ rookThreeGraphᶜ.Adj x y := by
        change (CliqueCovers.sideGraph H true).Adj x y ↔
          rookThreeGraphᶜ.Adj x y
        rw [hAnti]
      calc
        _ = ∑ y : rookVertex,
            if rookThreeGraphᶜ.Adj x y then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro y _
              simp only [hAdj y]
        _ = 4 := rook_four_internal_row_sums.2 x
  have hCross (x : rookVertex) :
      rookOutsideCrossDegree H x + 4 = D := by
    have hDeg : H.degree (true,x) = D := hReg (true,x)
    have hSplit := CliqueCovers.sideDegree_eq_two_row_sums H true x
    dsimp [rookOutsideCrossDegree]
    omega
  refine ⟨D - 4,?_,?_⟩
  · have hAtMostNine :
        rookOutsideCrossDegree H (0,0) ≤ 9 := by
      unfold rookOutsideCrossDegree
      calc
        (∑ y : rookVertex,
          if H.Adj (true,(0,0)) (false,y) then 1 else 0) ≤
          ∑ _y : rookVertex, (1 : ℕ) := by
            apply Finset.sum_le_sum
            intro y _
            split <;> omega
        _ = 9 := by decide
    have hh := hCross (0,0)
    omega
  · intro x
    have hh := hCross x
    omega

end EPPAIII.BlockSystems
