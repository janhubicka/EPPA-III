import EPPAIII.BlockSystems.TwoCliqueTaylorNamed
import EPPAIII.CliqueCovers.Basic

namespace EPPAIII.BlockSystems

/-- Relabel the layer by its XOR with the base colour. The two resulting
cliques are joined by the matching that preserves the base vertex. -/
noncomputable def twoCliqueMatchedGraph_iso_matchingCover {V : Type*} [Fintype V]
    (c : V → Bool) :
    twoCliqueMatchedGraph c true ≃g coverGraph 1 (Fintype.card V) .matching false := by
  let e := Fintype.equivFin V
  let f : (Bool × V) ≃ CoverVertex 1 (Fintype.card V) := {
    toFun u := (Bool.xor u.1 (c u.2), (0, e u.2))
    invFun w := (Bool.xor w.1 (c (e.symm w.2.2)), e.symm w.2.2)
    left_inv := by
      rintro ⟨b, x⟩
      change (Bool.xor (Bool.xor b (c x)) (c (e.symm (e x))), e.symm (e x)) = (b, x)
      rw [e.symm_apply_apply]
      cases b <;> cases c x <;> rfl
    right_inv := by
      rintro ⟨b, i, j⟩
      have hi : (0 : Fin 1) = i := Subsingleton.elim _ _
      change (Bool.xor (Bool.xor b (c (e.symm j))) (c (e.symm j)),
        ((0 : Fin 1), e (e.symm j))) = (b, (i, j))
      rw [hi, e.apply_symm_apply]
      cases b <;> cases c (e.symm j) <;> rfl }
  refine ⟨f, ?_⟩
  intro u v
  have hEq : u = v ↔ Bool.xor u.1 (c u.2) = Bool.xor v.1 (c v.2) ∧ u.2 = v.2 := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨hSide, hVertex⟩
      apply f.injective
      change (Bool.xor u.1 (c u.2), ((0 : Fin 1), e u.2)) =
        (Bool.xor v.1 (c v.2), ((0 : Fin 1), e v.2))
      rw [hSide, hVertex]
  change coverAdj .matching false
    (Bool.xor u.1 (c u.2), ((0 : Fin 1), e u.2))
    (Bool.xor v.1 (c v.2), ((0 : Fin 1), e v.2)) ↔ twoCliqueMatchedRel c true u v
  simp only [coverAdj, CrossType.rel, true_and,
    Equiv.apply_eq_iff_eq, twoCliqueMatchedRel, ne_eq, hEq]
  tauto

end EPPAIII.BlockSystems
