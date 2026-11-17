import EPPAIII.Primitive.PointStabilizerTransport

/-! # Full graph automorphism orders and singleton stabilizers -/

namespace EPPAIII.Primitive

/-- In a vertex-transitive graph the full automorphism group has order
the vertex count times the full point stabilizer order. -/
theorem graphAutomorphisms_card_eq_mul_pointStabilizer {W : Type*} [Finite W]
    (H : SimpleGraph W) (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H) (r : W) :
    Nat.card (graphAutomorphisms H) =
      Nat.card W * Nat.card (pointwiseGraphStabilizer H {r}) := by
  let A := hostPointwiseStabilizer H (∅ : Set W)
  let S := MulAction.stabilizer A r
  let O := MulAction.orbit A r
  let unfix : A ≃ graphAutomorphisms H := {
    toFun p := ⟨p.val, p.property.1⟩
    invFun p := ⟨p.val, p.property, fun x hx => False.elim hx⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  let fix : S ≃ hostPointwiseStabilizer H {r} := {
    toFun p := ⟨p.val.val, p.val.property.1, by rintro x rfl; exact p.property⟩
    invFun p := ⟨⟨p.val, p.property.1, fun x hx => False.elim hx⟩, p.property.2 r rfl⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hOrb : O = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨p, hp, hpr⟩ := hTrans r x
    exact ⟨⟨p, hp, fun z hz => False.elim hz⟩, hpr⟩
  have hCardO : Nat.card O = Nat.card W := by
    rw [hOrb]
    exact Nat.card_congr (Equiv.Set.univ W)
  have hCardS : Nat.card S = Nat.card (pointwiseGraphStabilizer H {r}) :=
    Nat.card_congr (fix.trans (pointwiseGraphStabilizerEquivHost H {r}).symm)
  rw [← Nat.card_congr unfix, ← hCardO, ← hCardS, ← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup A r).symm

end EPPAIII.Primitive
