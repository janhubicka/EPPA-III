import EPPAIII.Primitive.BinaryOrthogonalModels
import EPPAIII.Primitive.Subconstituents
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Init
import Mathlib.Data.Fintype.Basic

/-!
# Point constituents of the two affine orthogonal models

Translations move each root to zero. At zero, the two point predicates
are the singular and nonsingular six-dimensional point predicates.
-/

namespace EPPAIII.Primitive

open BlockSystems.BinaryFiveCycles

private def vectorQuadratic (plus : Bool) (x : Fin 64) : Nat :=
  if plus then quadPlus x.val else quadMinus x.val

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem vector_adj_difference :
    ∀ (plus : Bool) (a b : Fin 64), (vectorOrthogonalSixGraph plus).Adj a b ↔
      a ≠ b ∧ vectorQuadratic plus (a ^^^ b) = 0 := by
  decide

private theorem xor_assoc (a b c : Fin 64) :
    (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) :=
  Fin.xor_assoc (n := 6) rfl a b c

private def translate (root : Fin 64) : Equiv.Perm (Fin 64) where
  toFun x := x ^^^ root
  invFun x := x ^^^ root
  left_inv x := by
    change (x ^^^ root) ^^^ root = x
    rw [xor_assoc, Fin.xor_self, Fin.xor_zero]
  right_inv x := by
    change (x ^^^ root) ^^^ root = x
    rw [xor_assoc, Fin.xor_self, Fin.xor_zero]

/-- Translation by the root is a graph automorphism of the affine model. -/
def affineOrthogonalTranslation (plus : Bool) (root : Fin 64) :
    vectorOrthogonalSixGraph plus ≃g vectorOrthogonalSixGraph plus where
  toEquiv := translate root
  map_rel_iff' := by
    intro a b
    have hCancel : translate root a ^^^ translate root b = a ^^^ b := by
      change (a ^^^ root) ^^^ (b ^^^ root) = a ^^^ b
      rw [xor_assoc, Fin.xor_comm b root, ← xor_assoc root root b, Fin.xor_self,
        Fin.xor_comm 0 b, Fin.xor_zero]
    rw [vector_adj_difference, vector_adj_difference, hCancel]
    exact and_congr (not_congr (translate root).injective.eq_iff) Iff.rfl

@[simp] theorem affineOrthogonalTranslation_root (plus : Bool) (root : Fin 64) :
    affineOrthogonalTranslation plus root root = 0 :=
  Fin.xor_self root

private theorem local_zero_predicate :
    ∀ (plus : Bool) (x : Fin 64), (vectorOrthogonalSixGraph plus).Adj 0 x ↔
      isOrthogonalVertex plus true x.val := by
  decide

private theorem nonlocal_zero_predicate :
    ∀ (plus : Bool) (x : Fin 64), (0 ≠ x ∧ ¬ (vectorOrthogonalSixGraph plus).Adj 0 x) ↔
      isOrthogonalVertex plus false x.val := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem point_adjacency :
    ∀ (plus singular : Bool) (a b : OrthogonalSixVertex plus singular),
      (vectorOrthogonalSixGraph plus).Adj a.val b.val ↔
        (orthogonalSixGraph plus singular).Adj a b := by
  decide

/-- The first constituent of the affine model is the singular point graph. -/
def affineOrthogonalLocalIso (plus : Bool) (root : Fin 64) :
    localGraph (vectorOrthogonalSixGraph plus) root ≃g orthogonalSixGraph plus true where
  toEquiv := (affineOrthogonalTranslation plus root).toEquiv.subtypeEquiv fun x => by
    change (vectorOrthogonalSixGraph plus).Adj root x ↔
      isOrthogonalVertex plus true (affineOrthogonalTranslation plus root x).val
    rw [← local_zero_predicate,
      ← affineOrthogonalTranslation_root plus root]
    exact (affineOrthogonalTranslation plus root).map_rel_iff.symm
  map_rel_iff' := by
    intro a b
    exact (point_adjacency plus true _ _).symm.trans
      (affineOrthogonalTranslation plus root).map_rel_iff

/-- The second constituent of the affine model is the nonsingular point graph. -/
def affineOrthogonalNonlocalIso (plus : Bool) (root : Fin 64) :
    nonlocalGraph (vectorOrthogonalSixGraph plus) root ≃g orthogonalSixGraph plus false where
  toEquiv := (affineOrthogonalTranslation plus root).toEquiv.subtypeEquiv fun x => by
    change (root ≠ x ∧ ¬ (vectorOrthogonalSixGraph plus).Adj root x) ↔
      isOrthogonalVertex plus false (affineOrthogonalTranslation plus root x).val
    rw [← nonlocal_zero_predicate, ← affineOrthogonalTranslation_root plus root]
    exact and_congr (not_congr
      (affineOrthogonalTranslation plus root).toEquiv.injective.eq_iff.symm)
      (not_congr (affineOrthogonalTranslation plus root).map_rel_iff.symm)
  map_rel_iff' := by
    intro a b
    exact (point_adjacency plus false _ _).symm.trans
      (affineOrthogonalTranslation plus root).map_rel_iff

end EPPAIII.Primitive
