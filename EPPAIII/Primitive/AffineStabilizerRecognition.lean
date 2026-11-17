import EPPAIII.Primitive.AffineLineExclusionFromSubdegrees
import EPPAIII.Primitive.FullGraphStabilizerOrder
import EPPAIII.Primitive.RankThree

/-! # Recovering affine pair stabilizers from published group and subdegree data -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems EPPAIII.CliqueCovers
open SimpleGraph

/-- The rank-three orbit over a fixed vertex has size k for an edge
and n - k - 1 for a nonedge with distinct endpoints. -/
theorem srg_subdegree_eq {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n k l μ : ℕ}
    (h : H.IsSRGWith n k l μ) (x y : W) :
    Nat.card {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} =
      if H.Adj x y then k else n - k - 1 := by
  by_cases hxy : H.Adj x y
  · let e : {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} ≃ H.neighborSet x :=
      { toFun := fun z => ⟨z.val, z.property.2.mp hxy⟩
        invFun := fun z => ⟨z.val, z.property.ne, iff_of_true hxy z.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, H.card_neighborSet_eq_degree,
      h.regular x, ite_eq_left hxy]
  · let e : {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} ≃ Hᶜ.neighborSet x :=
      { toFun := fun z => ⟨z.val, z.property.1, fun hz => hxy (z.property.2.mpr hz)⟩
        invFun := fun z => ⟨z.val, z.property.1, iff_of_false hxy z.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Hᶜ.card_neighborSet_eq_degree,
      h.compl.regular x, ite_eq_right hxy]

/-- A full pair stabilizer order times the corresponding rank-three subdegree
is the full singleton stabilizer order. -/
theorem hostPairStabilizer_card_mul_srg_subdegree
    {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hRank : HasRankThreeAutAction H) {n k l μ : ℕ} (hSRG : H.IsSRGWith n k l μ)
    (x y : W) (hxy : x ≠ y) :
    Nat.card (hostPointwiseStabilizer H {x, y}) * (if H.Adj x y then k else n - k - 1) =
      Nat.card (hostPointwiseStabilizer H {x}) := by
  rw [← srg_subdegree_eq H hSRG x y]
  exact hostPairStabilizer_card_mul_subdegree H x y hxy
    (fun z hz => rankThree_point_stabilizer H hRank x y z hxy hz)

/-- The same orbit–stabilizer formula for the stabilizers defined inside the
full graph automorphism group. -/
theorem pointwiseGraphStabilizer_card_mul_srg_subdegree
    {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hRank : HasRankThreeAutAction H) {n k l μ : ℕ} (hSRG : H.IsSRGWith n k l μ)
    (x y : W) (hxy : x ≠ y) :
    Nat.card (pointwiseGraphStabilizer H {x, y}) * (if H.Adj x y then k else n - k - 1) =
      Nat.card (pointwiseGraphStabilizer H {x}) := by
  rw [Nat.card_congr (pointwiseGraphStabilizerEquivHost H {x, y}),
    Nat.card_congr (pointwiseGraphStabilizerEquivHost H {x})]
  exact hostPairStabilizer_card_mul_srg_subdegree H hRank hSRG x y hxy

/-- A full graph automorphism group order supplies the exact order of every
point stabilizer in a transitive graph. -/
theorem card_pointwiseGraphStabilizer_singleton_of_full_order {W : Type*} [Finite W]
    (H : SimpleGraph W) (hTrans : HasTransitiveGraphAutomorphisms H) (r : W) {b : ℕ}
    (hOrder : Nat.card (graphAutomorphisms H) = Nat.card W * b) :
    Nat.card (pointwiseGraphStabilizer H {r}) = b := by
  have : Nonempty W := ⟨r⟩
  have hPositive : 0 < Nat.card W := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hPositive
    ((graphAutomorphisms_card_eq_mul_pointStabilizer H hTrans r).symm.trans hOrder)

/-- The full group bound likewise suffices when a row only needs an upper
bound on its point stabilizer. -/
theorem card_hostPointwiseStabilizer_singleton_le_of_full_order {W : Type*} [Finite W]
    (H : SimpleGraph W) (hTrans : HasTransitiveGraphAutomorphisms H) (r : W) {b : ℕ}
    (hOrder : Nat.card (graphAutomorphisms H) ≤ Nat.card W * b) :
    Nat.card (hostPointwiseStabilizer H {r}) ≤ b := by
  have : Nonempty W := ⟨r⟩
  have hPositive : 0 < Nat.card W := Nat.card_pos
  rw [← Nat.card_congr (pointwiseGraphStabilizerEquivHost H {r})]
  rw [graphAutomorphisms_card_eq_mul_pointStabilizer H hTrans r] at hOrder
  exact Nat.le_of_mul_le_mul_left hOrder hPositive

/-- Subdegree lower bounds and a point-stabilizer bound at one root provide a
uniform bound over all ordered pairs. -/
theorem hostPairStabilizer_le_of_srg_and_singleton_bound
    {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hRank : HasRankThreeAutAction H) {n k l μ d b : ℕ} (hSRG : H.IsSRGWith n k l μ)
    (hd : 0 < d) (hEdge : d ≤ k) (hNonedge : d ≤ n - k - 1)
    (r : W) (hPoint : Nat.card (hostPointwiseStabilizer H {r}) ≤ d * b)
    (x y : W) (hxy : x ≠ y) : Nat.card (hostPointwiseStabilizer H {x, y}) ≤ b := by
  have hSub : d ≤ Nat.card {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} := by
    rw [srg_subdegree_eq H hSRG x y]
    split_ifs <;> assumption
  have hPointX := (card_hostPointwiseStabilizer_singleton_of_transitive H hRank.2.2.1 x r).trans_le hPoint
  exact hostPairStabilizer_le_of_pointStabilizer_and_subdegree H x y hxy
    (fun z hz => rankThree_point_stabilizer H hRank x y z hxy hz) hd hSub hPointX

end EPPAIII.Primitive
