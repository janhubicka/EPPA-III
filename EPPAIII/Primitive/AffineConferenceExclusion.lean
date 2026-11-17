import EPPAIII.Primitive.AffineLineExclusionFromSubdegrees
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-! # Pair stabilizers for the finite affine conference rows -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- Both nontrivial subdegrees of a conference host equal its valency. -/
theorem conference_subdegree_eq {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n k l μ : ℕ}
    (h : H.IsSRGWith n k l μ) (hn : n = 2 * k + 1)
    (x y : W) :
    Nat.card {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} = k := by
  by_cases hxy : H.Adj x y
  · let e : {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} ≃ H.neighborSet x :=
      { toFun := fun z => ⟨z.val, z.property.2.mp hxy⟩
        invFun := fun z => ⟨z.val, z.property.ne, iff_of_true hxy z.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, H.card_neighborSet_eq_degree,
      h.regular x]
  · let e : {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} ≃ Hᶜ.neighborSet x :=
      { toFun := fun z => ⟨z.val, z.property.1, fun hz => hxy (z.property.2.mpr hz)⟩
        invFun := fun z => ⟨z.val, z.property.1, iff_of_false hxy z.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Hᶜ.card_neighborSet_eq_degree,
      h.compl.regular x]
    omega

/-- The two-anchor obstruction for conference rows of sufficiently large order.
The hypotheses are the full point-stabilizer bound and rank-three transitivity
on ordered pairs of the same status. -/
theorem conference_not_eppa_of_point_stabilizers {V W : Type*} [Finite V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj] (e : V ↪ W) {n k l μ m : ℕ}
    (h : H.IsSRGWith n k l μ) (hn : n = 2 * k + 1) (hk : 0 < k)
    (hOrder : 8 * m + 4 < n) (hLarge : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y z : W, x ≠ y → x ≠ z → (H.Adj x y ↔ H.Adj x z) →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z)
    (hPoint : ∀ x : W, Nat.card (hostPointwiseStabilizer H {x}) ≤ k * m) :
    ¬ IsEPPAEmbedding G H e := by
  apply not_eppa_embedding_of_pair_stabilizers G H e hLarge (k := m)
    (by simpa only [Nat.card_eq_fintype_card, h.card] using hOrder)
  intro x y hxy
  exact hostPairStabilizer_le_of_pointStabilizer_and_subdegree H x y hxy
    (fun z hz => hTrans x y z hxy hz) hk
    (by rw [conference_subdegree_eq H h hn x y]) (hPoint x)

/-- The order-81 conference row uses three anchors and only the same
point-stabilizer bound, as the valency is forty. -/
theorem conference_eightyOne_not_eppa {V W : Type*} [Finite V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj] (e : V ↪ W)
    (h : H.IsSRGWith 81 40 19 20)
    (hLarge : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y z : W, x ≠ y → x ≠ z → (H.Adj x y ↔ H.Adj x z) →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z)
    (hPoint : ∀ x : W, Nat.card (hostPointwiseStabilizer H {x}) ≤ 480) :
    ¬ IsEPPAEmbedding G H e := by
  apply not_eppa_embedding_order_eightyOne_of_point_stabilizers G H e hLarge
    (Nat.card_eq_fintype_card.trans h.card) hTrans hPoint
  intro x y hxy
  rw [conference_subdegree_eq H h (by decide) x y]

/-- The four affine conference rows that pass the order-and-degree screen. -/
inductive AffineConferenceRow
  | order49
  | order81
  | order529
  | order2209

/-- Both orientations have the same strongly regular parameters. -/
def AffineConferenceRow.parameters (row : AffineConferenceRow) : ℕ × ℕ × ℕ × ℕ :=
  match row with
  | .order49 => (49, 24, 11, 12)
  | .order81 => (81, 40, 19, 20)
  | .order529 => (529, 264, 131, 132)
  | .order2209 => (2209, 1104, 551, 552)

/-- Bounds for the full point stabilizers cited from Brouwer–Van Maldeghem,
Sections 10.18, 10.30, 10.70 and 10.86. -/
def AffineConferenceRow.pointBound (row : AffineConferenceRow) : ℕ :=
  match row with
  | .order49 => 96
  | .order81 => 480
  | .order529 => 528
  | .order2209 => 2208

/-- None of the four conference rows admits an EPPA selection of at least half
the host order, given the published full point-stabilizer bounds. -/
theorem affineConference_not_eppa {V W : Type*} [Finite V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (row : AffineConferenceRow)
    (h : let p := row.parameters; H.IsSRGWith p.1 p.2.1 p.2.2.1 p.2.2.2)
    (hLarge : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y z : W, x ≠ y → x ≠ z → (H.Adj x y ↔ H.Adj x z) →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z)
    (hPoint : ∀ x : W, Nat.card (hostPointwiseStabilizer H {x}) ≤ row.pointBound) :
    ¬ IsEPPAEmbedding G H e := by
  cases row
  · exact conference_not_eppa_of_point_stabilizers G H e (m := 4) h
      (by decide) (by decide) (by decide) hLarge hTrans hPoint
  · exact conference_eightyOne_not_eppa G H e h hLarge hTrans hPoint
  · exact conference_not_eppa_of_point_stabilizers G H e (m := 2) h
      (by decide) (by decide) (by decide) hLarge hTrans hPoint
  · exact conference_not_eppa_of_point_stabilizers G H e (m := 2) h
      (by decide) (by decide) (by decide) hLarge hTrans hPoint

end EPPAIII.Primitive
