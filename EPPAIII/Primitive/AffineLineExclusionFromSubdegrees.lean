import EPPAIII.Primitive.AffineLineExclusion

/-! # Two-point stabilizer orders from the rank-three subdegrees -/

namespace EPPAIII.Primitive

/-- The point stabilizer orbit of `y` is the other vertices of its status
with respect to `x` when the action is transitive on ordered pairs of that status. -/
theorem hostPairStabilizer_card_mul_subdegree {W : Type*} [Finite W]
    (H : SimpleGraph W) (x y : W) (hxy : x ≠ y)
    (hTrans : ∀ z, x ≠ z → (H.Adj x y ↔ H.Adj x z) →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z) :
    Nat.card (hostPointwiseStabilizer H {x, y}) *
      Nat.card {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} =
      Nat.card (hostPointwiseStabilizer H {x}) := by
  let R := hostPointwiseStabilizer H ({x} : Set W)
  let D : Set W := {z : W | x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)}
  have hOrbit : MulAction.orbit R y = D := by
    ext z
    constructor
    · rintro ⟨q, hq⟩
      change q.val y = z at hq
      have hx : q.val x = x := q.property.2 x rfl
      change x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)
      exact ⟨by simpa only [hx, hq] using q.val.injective.ne hxy,
        by simpa only [hx, hq] using q.property.1 x y⟩
    · intro hz
      obtain ⟨q, hq, hx, hy⟩ := hTrans z hz.1 hz.2
      refine ⟨⟨q, hq, ?_⟩, hy⟩
      intro a ha
      have ha' : a = x := ha
      simpa only [ha'] using hx
  let T := MulAction.stabilizer R y
  let Q := hostPointwiseStabilizer H ({x, y} : Set W)
  have hEquiv : T ≃ Q :=
    { toFun := fun q => ⟨q.val.val, q.val.property.1, by
        have hx : q.val.val x = x := q.val.property.2 x rfl
        have hy : q.val.val y = y := q.property
        rintro a (rfl | rfl)
        · exact hx
        · exact hy⟩
      invFun := fun q => ⟨⟨q.val, q.property.1, by
          intro a ha
          have ha' : a = x := ha
          rw [ha']
          exact q.property.2 x (Or.inl rfl)⟩,
        q.property.2 y (Or.inr rfl)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change Nat.card Q * Nat.card D = Nat.card R
  rw [← hOrbit, ← Nat.card_congr hEquiv, Nat.mul_comm, ← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup R y)

/-- Point stabilizer orders and the two subdegrees suffice to check any of
these Peisert pair-stabilizer bounds without enumerating automorphisms. -/
theorem hostPairStabilizer_le_of_pointStabilizer_and_subdegree
    {W : Type*} [Finite W] (H : SimpleGraph W) (x y : W) (hxy : x ≠ y)
    (hTrans : ∀ z, x ≠ z → (H.Adj x y ↔ H.Adj x z) →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z)
    {d k : ℕ} (hd : 0 < d)
    (hSubdegree : d ≤ Nat.card {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)})
    (hPoint : Nat.card (hostPointwiseStabilizer H {x}) ≤ d * k) :
    Nat.card (hostPointwiseStabilizer H {x, y}) ≤ k := by
  have hCard := hostPairStabilizer_card_mul_subdegree H x y hxy hTrans
  have hMul : Nat.card (hostPointwiseStabilizer H {x, y}) * d ≤ k * d := calc
    _ ≤ _ := Nat.mul_le_mul_left _ hSubdegree
    _ = Nat.card (hostPointwiseStabilizer H {x}) := hCard
    _ ≤ d * k := hPoint
    _ = k * d := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hMul hd

/-- An order-81 host with the Peisert point stabilizer and subdegree bounds
has no EPPA selected copy of at least half the vertices. -/
theorem not_eppa_embedding_order_eightyOne_of_point_stabilizers {V W : Type*}
    [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hLarge : Nat.card W ≤ 2 * Nat.card V) (hOrder : Nat.card W = 81)
    (hTrans : ∀ x y z, x ≠ y → x ≠ z → (H.Adj x y ↔ H.Adj x z) →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z)
    (hPoint : ∀ x : W, Nat.card (hostPointwiseStabilizer H {x}) ≤ 480)
    (hSubdegree : ∀ x y : W, x ≠ y →
      40 ≤ Nat.card {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)}) :
    ¬ IsEPPAEmbedding G H e := by
  apply not_eppa_embedding_order_eightyOne_of_pair_stabilizers G H e hLarge hOrder
  intro x y hxy
  exact hostPairStabilizer_le_of_pointStabilizer_and_subdegree H x y hxy
    (fun z hz => hTrans x y z hxy hz) (d := 40) (by decide) (hSubdegree x y hxy) (hPoint x)

end EPPAIII.Primitive
