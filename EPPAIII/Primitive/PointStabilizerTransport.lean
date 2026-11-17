import EPPAIII.CliqueCovers.TransitiveHalfEdges
import EPPAIII.Primitive.AffineLineExclusion
import EPPAIII.Primitive.LocalSections

/-! # Transport of full pointwise graph stabilizers -/

namespace EPPAIII.Primitive

/-- Conjugation relabels the full group fixing a given vertex set pointwise. -/
def hostPointwiseStabilizerEquiv {W X : Type*}
    {H : SimpleGraph W} {K : SimpleGraph X} (φ : H ≃g K) (A : Set W) :
    hostPointwiseStabilizer H A ≃ hostPointwiseStabilizer K (φ '' A) := by
  apply Equiv.subtypeEquiv φ.toEquiv.permCongr
  intro p
  change (IsGraphAutomorphism H p ∧ ∀ x ∈ A, p x = x) ↔
    (IsGraphAutomorphism K (φ.toEquiv.permCongr p) ∧
      ∀ y ∈ φ '' A, φ.toEquiv.permCongr p y = y)
  constructor
  · rintro ⟨hp, hFix⟩
    constructor
    · intro a b
      change K.Adj a b ↔ K.Adj (φ (p (φ.symm a))) (φ (p (φ.symm b)))
      rw [φ.map_rel_iff, ← hp, ← φ.map_rel_iff, φ.apply_symm_apply, φ.apply_symm_apply]
    · rintro _ ⟨x, hx, rfl⟩
      change φ (p (φ.symm (φ x))) = φ x
      rw [φ.symm_apply_apply, hFix x hx]
  · rintro ⟨hp, hFix⟩
    constructor
    · intro a b
      have h := hp (φ a) (φ b)
      change K.Adj (φ a) (φ b) ↔
        K.Adj (φ (p (φ.symm (φ a)))) (φ (p (φ.symm (φ b)))) at h
      rw [φ.symm_apply_apply, φ.symm_apply_apply, φ.map_rel_iff, φ.map_rel_iff] at h
      exact h
    · intro x hx
      have h := hFix (φ x) ⟨x, hx, rfl⟩
      change φ (p (φ.symm (φ x))) = φ x at h
      rw [φ.symm_apply_apply] at h
      exact φ.injective h

/-- The two full pointwise graph stabilizer representations have the same elements. -/
def pointwiseGraphStabilizerEquivHost {W : Type*} (H : SimpleGraph W) (A : Set W) :
    pointwiseGraphStabilizer H A ≃ hostPointwiseStabilizer H A where
  toFun p := ⟨p.val.val, p.val.property, p.property⟩
  invFun p := ⟨⟨p.val, p.property.1⟩, p.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A graph isomorphism transports singleton stabilizer orders. -/
theorem card_pointwiseGraphStabilizer_singleton_of_iso {W X : Type*}
    {H : SimpleGraph W} {K : SimpleGraph X} (φ : H ≃g K) (r : W) :
    Nat.card (pointwiseGraphStabilizer H {r}) =
      Nat.card (pointwiseGraphStabilizer K {φ r}) := by
  rw [Nat.card_congr (pointwiseGraphStabilizerEquivHost H {r}),
    Nat.card_congr (pointwiseGraphStabilizerEquivHost K {φ r}),
    Nat.card_congr (hostPointwiseStabilizerEquiv φ {r}), Set.image_singleton]

/-- All singleton stabilizers of a vertex-transitive graph have the same order. -/
theorem card_pointwiseGraphStabilizer_singleton_of_transitive {W : Type*}
    (H : SimpleGraph W) (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (r s : W) : Nat.card (pointwiseGraphStabilizer H {r}) =
      Nat.card (pointwiseGraphStabilizer H {s}) := by
  obtain ⟨p, hp, hrs⟩ := hTrans r s
  let φ : H ≃g H := ⟨p, fun {x y} => (hp x y).symm⟩
  have h : φ r = s := hrs
  simpa only [h] using card_pointwiseGraphStabilizer_singleton_of_iso φ r

/-- All singleton stabilizers of a vertex-transitive graph have the same order,
using their representation inside the full permutation group. -/
theorem card_hostPointwiseStabilizer_singleton_of_transitive {W : Type*}
    (H : SimpleGraph W) (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (r s : W) : Nat.card (hostPointwiseStabilizer H {r}) =
      Nat.card (hostPointwiseStabilizer H {s}) := by
  rw [← Nat.card_congr (pointwiseGraphStabilizerEquivHost H {r}),
    ← Nat.card_congr (pointwiseGraphStabilizerEquivHost H {s})]
  exact card_pointwiseGraphStabilizer_singleton_of_transitive H hTrans r s

end EPPAIII.Primitive
