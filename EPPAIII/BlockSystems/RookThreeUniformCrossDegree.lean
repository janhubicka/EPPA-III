import EPPAIII.BlockSystems.RookThreePairOutsideGraph

/-!
# Uniform cross-degree from rook graphs on both halves

In a transitive eighteen-vertex EPPA host of R3, the selected
half is 4-regular. When the outside graph is R3 or its complement,
it is also 4-regular. Every outside vertex therefore has exactly
D−4 neighbours in the selected half, where D is the uniform host
degree. This proves the uniform-cross-degree reduction needed
before applying the k=0..4 exceptional classification.

The lemma is proved in labelled Bool×R3 coordinates; actual
imprimitive host coordinates are constructed separately.
-/

namespace EPPAIII.BlockSystems

/-- Neighbours of a top rook vertex in the bottom half. -/
noncomputable def rookOutsideCrossDegree
    (H : SimpleGraph (Bool × rookVertex)) (x : rookVertex) : ℕ := by
  classical
  exact ((Finset.univ : Finset rookVertex).filter
    (fun y => H.Adj (true,x) (false,y))).card

/-- Both R3 and its complement have valency four. -/
theorem rook_and_complement_degree_four :
    (∀ x : rookVertex, rookThreeGraph.degree x = 4) ∧
    (∀ x : rookVertex, rookThreeGraphᶜ.degree x = 4) := by
  constructor
  · intro x
    change ((Finset.univ : Finset rookVertex).filter
      (fun y => rookThreeGraph.Adj x y)).card = 4
    exact rookThreeGraph_degree_four x
  · decide

/-- In a transitive host with bottom R3 and top R3 or
anti-R3, the cross-degree of every outside vertex is
uniform and at most nine. -/
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
  have hTopDegree (x : rookVertex) :
      (CliqueCovers.sideGraph H true).degree x = 4 := by
    rcases hTop with hRook | hComplement
    · rw [hRook]
      exact rook_and_complement_degree_four.1 x
    · rw [hComplement]
      exact rook_and_complement_degree_four.2 x
  have hCrossSum (x : rookVertex) :
      rookOutsideCrossDegree H x =
        ∑ y : rookVertex,
          if H.Adj (true,x) (false,y) then 1 else 0 := by
    unfold rookOutsideCrossDegree
    simpa using
      (Finset.sum_boole
        (p := fun y : rookVertex => H.Adj (true,x) (false,y))
        (s := Finset.univ) (R := ℕ)).symm
  have hInsideSum (x : rookVertex) :
      (∑ y : rookVertex,
          if H.Adj (true,x) (true,y) then 1 else 0) = 4 := by
    calc
      _ = ((Finset.univ : Finset rookVertex).filter
          (fun y => H.Adj (true,x) (true,y))).card := by
            simpa using
              (Finset.sum_boole
                (p := fun y : rookVertex => H.Adj (true,x) (true,y))
                (s := Finset.univ) (R := ℕ))
      _ = (CliqueCovers.sideGraph H true).degree x := by
            rw [SimpleGraph.degree,
              (CliqueCovers.sideGraph H true).neighborFinset_eq_filter]
            rfl
      _ = 4 := hTopDegree x
  have hRow (x : rookVertex) :
      rookOutsideCrossDegree H x + 4 = D := by
    have hDeg : H.degree (true,x) = D := hReg (true,x)
    have hSplit := CliqueCovers.sideDegree_eq_two_row_sums H true x
    rw [hCrossSum x, hInsideSum x] at *
    omega
  refine ⟨D - 4,?_,?_⟩
  · have hSmall :
        rookOutsideCrossDegree H (0,0) ≤ 9 := by
      unfold rookOutsideCrossDegree
      calc
        _ ≤ (Finset.univ : Finset rookVertex).card :=
          Finset.card_filter_le _ _
        _ = 9 := by decide
    omega
  · intro x
    have h := hRow x
    omega

end EPPAIII.BlockSystems
