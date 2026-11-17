import EPPAIII.Primitive.BinaryOrthogonalModels
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Orthogonal sums with binary hyperbolic pairs -/

namespace EPPAIII.Primitive

open BlockSystems.BinaryFiveCycles
open scoped BigOperators

/-- Extra hyperbolic coordinates, paired in their given order. -/
abbrev BinaryHyperbolic (m : ℕ) := (Fin m → ZMod 2) × (Fin m → ZMod 2)

private def hyperbolicQ {m : ℕ} (x : BinaryHyperbolic m) : ZMod 2 :=
  ∑ i, x.1 i * x.2 i

private def hyperbolicB {m : ℕ} (x y : BinaryHyperbolic m) : ZMod 2 :=
  ∑ i, (x.1 i * y.2 i + y.1 i * x.2 i)

private theorem hyperbolicB_comm {m : ℕ} (x y : BinaryHyperbolic m) :
    hyperbolicB x y = hyperbolicB y x := by
  simp only [hyperbolicB, add_comm]

private def baseQ (plus : Bool) (x : Fin 64) : ZMod 2 :=
  (if plus then quadPlus x.val else quadMinus x.val : ℕ)

private def baseB (plus : Bool) (x y : Fin 64) : ZMod 2 :=
  (if plus then polarPlus x.val y.val else polarMinus x.val y.val : ℕ)

private theorem baseB_comm (plus : Bool) (x y : Fin 64) :
    baseB plus x y = baseB plus y x := by
  cases plus
  · simp only [baseB, Bool.false_eq_true, ↓reduceIte, polarMinus]
    congr 2
    ac_rfl
  · simp only [baseB, ↓reduceIte, polarPlus]
    congr 2
    ac_rfl

private theorem cast_mod_two_eq_zero {a : ℕ} (ha : a < 2) :
    (a : ZMod 2) = 0 ↔ a = 0 := by
  rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt ha]

private theorem baseQ_zero (plus : Bool) (x : Fin 64) :
    baseQ plus x = 0 ↔ (if plus then quadPlus x.val else quadMinus x.val) = 0 :=
  cast_mod_two_eq_zero (by cases plus <;> exact Nat.mod_lt _ (by decide))

private theorem baseB_zero (plus : Bool) (x y : Fin 64) :
    baseB plus x y = 0 ↔ (if plus then polarPlus x.val y.val else polarMinus x.val y.val) = 0 :=
  cast_mod_two_eq_zero (by cases plus <;> exact Nat.mod_lt _ (by decide))

private def extensionQ {m : ℕ} (plus : Bool) (x : Fin 64 × BinaryHyperbolic m) : ZMod 2 :=
  baseQ plus x.1 + hyperbolicQ x.2

private def extensionB {m : ℕ} (plus : Bool) (x y : Fin 64 × BinaryHyperbolic m) : ZMod 2 :=
  baseB plus x.1 y.1 + hyperbolicB x.2 y.2

private theorem extensionB_comm {m : ℕ} (plus : Bool) (x y : Fin 64 × BinaryHyperbolic m) :
    extensionB plus x y = extensionB plus y x := by
  rw [extensionB, extensionB, baseB_comm plus x.1 y.1, hyperbolicB_comm x.2 y.2]

/-- Perpendicularity model of the singular or nonsingular vertices in the
six-dimensional reference form extended by `m` hyperbolic pairs. -/
abbrev BinaryOrthogonalExtendedVertex (plus singular : Bool) (m : ℕ) :=
  {x : Fin 64 × BinaryHyperbolic m // x ≠ 0 ∧ (extensionQ plus x = 0 ↔ singular = true)}

/-- The direct-sum perpendicularity graph. -/
def binaryOrthogonalExtendedGraph (plus singular : Bool) (m : ℕ) :
    SimpleGraph (BinaryOrthogonalExtendedVertex plus singular m) where
  Adj x y := x ≠ y ∧ extensionB plus x.val y.val = 0
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, by simpa only [extensionB_comm plus y.val x.val] using h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The direct-sum affine orthogonal graph, using the polarized difference
of two vectors in characteristic two. -/
def binaryAffineOrthogonalExtendedGraph (plus : Bool) (m : ℕ) :
    SimpleGraph (Fin 64 × BinaryHyperbolic m) where
  Adj x y := x ≠ y ∧ (extensionQ plus x + extensionQ plus y + extensionB plus x y) = 0
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, by
      simpa only [extensionB_comm plus y x, add_comm (extensionQ plus y) (extensionQ plus x)]
        using h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem zeroExtensionQ (plus : Bool) (x : Fin 64) (m : ℕ) :
    extensionQ plus (x, (0 : BinaryHyperbolic m)) = baseQ plus x := by
  simp [extensionQ, hyperbolicQ]

private theorem zeroExtensionB (plus : Bool) (x y : Fin 64) (m : ℕ) :
    extensionB plus (x, (0 : BinaryHyperbolic m)) (y, 0) = baseB plus x y := by
  simp [extensionB, hyperbolicB]

private def orthogonalZeroExtension (plus singular : Bool) (m : ℕ)
    (x : OrthogonalSixVertex plus singular) :
    BinaryOrthogonalExtendedVertex plus singular m :=
  ⟨(x.val, 0), fun h => (Nat.ne_of_gt x.property.1) (congrArg Fin.val (congrArg Prod.fst h)),
    by rw [zeroExtensionQ, baseQ_zero]; exact x.property.2.2⟩

/-- Zero extension preserves the norm class and all perpendicularities. -/
def orthogonalSix_into_hyperbolic_extension (plus singular : Bool) (m : ℕ) :
    orthogonalSixGraph plus singular ↪g binaryOrthogonalExtendedGraph plus singular m where
  toFun := orthogonalZeroExtension plus singular m
  inj' := fun _ _ h => Subtype.ext (congrArg (Prod.fst ∘ Subtype.val) h)
  map_rel_iff' := by
    intro x y
    change (orthogonalZeroExtension plus singular m x ≠ orthogonalZeroExtension plus singular m y ∧
      extensionB plus (x.val, (0 : BinaryHyperbolic m)) (y.val, 0) = 0) ↔
      (x ≠ y ∧ (if plus then polarPlus x.val.val y.val.val else polarMinus x.val.val y.val.val) = 0)
    rw [zeroExtensionB, baseB_zero]
    exact and_congr (not_congr ⟨fun h => Subtype.ext (congrArg (Prod.fst ∘ Subtype.val) h),
      fun h => congrArg _ h⟩) Iff.rfl

private theorem base_affine_zero (plus : Bool) (x y : Fin 64) :
    baseQ plus x + baseQ plus y + baseB plus x y = 0 ↔
      (if plus then (quadPlus x + quadPlus y + polarPlus x y) % 2
        else (quadMinus x + quadMinus y + polarMinus x y) % 2) = 0 := by
  cases plus <;> simp only [baseQ, baseB, Bool.false_eq_true, ↓reduceIte] <;>
    rw [← Nat.cast_add, ← Nat.cast_add, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

/-- Zero extension preserves singular differences. -/
def affineOrthogonalSix_into_hyperbolic_extension (plus : Bool) (m : ℕ) :
    vectorOrthogonalSixGraph plus ↪g binaryAffineOrthogonalExtendedGraph plus m where
  toFun x := (x, 0)
  inj' := fun _ _ h => congrArg Prod.fst h
  map_rel_iff' := by
    intro x y
    change ((x, (0 : BinaryHyperbolic m)) ≠ (y, 0) ∧
      extensionQ plus (x, (0 : BinaryHyperbolic m)) + extensionQ plus (y, (0 : BinaryHyperbolic m)) +
        extensionB plus (x, (0 : BinaryHyperbolic m)) (y, 0) = 0) ↔
      (x ≠ y ∧ (if plus then (quadPlus x + quadPlus y + polarPlus x y) % 2
        else (quadMinus x + quadMinus y + polarMinus x y) % 2) = 0)
    rw [zeroExtensionQ, zeroExtensionQ, zeroExtensionB, base_affine_zero]
    exact and_congr (not_congr ⟨fun h => congrArg Prod.fst h, fun h => congrArg (fun z => (z, 0)) h⟩)
      Iff.rfl

/-- Nonzero four-dimensional binary symplectic vectors. -/
abbrev BinarySymplecticFourVertex := {x : Fin 16 // x ≠ 0}

private theorem symplecticFour_comm (a b : ℕ) : symplecticFour a b = symplecticFour b a := by
  unfold symplecticFour
  ac_rfl

/-- The perpendicularity model of the four-dimensional binary symplectic graph. -/
def binarySymplecticFourGraph : SimpleGraph BinarySymplecticFourVertex where
  Adj x y := x ≠ y ∧ symplecticFour x.val.val y.val.val = 0
  symm := ⟨fun _ _ h => ⟨h.1.symm, (symplecticFour_comm _ _).trans h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Extend the four-dimensional symplectic space by `m` hyperbolic pairs. -/
abbrev BinarySymplecticExtendedVertex (m : ℕ) := {x : Fin 16 × BinaryHyperbolic m // x ≠ 0}

private def symplecticExtensionB {m : ℕ} (x y : Fin 16 × BinaryHyperbolic m) : ZMod 2 :=
  (symplecticFour x.1.val y.1.val : ℕ) + hyperbolicB x.2 y.2

def binarySymplecticExtendedGraph (m : ℕ) : SimpleGraph (BinarySymplecticExtendedVertex m) where
  Adj x y := x ≠ y ∧ symplecticExtensionB x.val y.val = 0
  symm := by
    constructor
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    simpa only [symplecticExtensionB, symplecticFour_comm y.val.1.val x.val.1.val,
      hyperbolicB_comm y.val.2 x.val.2] using h.2
  loopless := ⟨fun _ h => h.1 rfl⟩

private def symplecticZeroExtension (m : ℕ) (x : BinarySymplecticFourVertex) :
    BinarySymplecticExtendedVertex m :=
  ⟨(x.val, 0), fun h => x.property (congrArg Prod.fst h)⟩

/-- The symplectic zero extension preserves perpendicularity. -/
def symplecticFour_into_hyperbolic_extension (m : ℕ) :
    binarySymplecticFourGraph ↪g binarySymplecticExtendedGraph m where
  toFun := symplecticZeroExtension m
  inj' := fun _ _ h => Subtype.ext (congrArg (Prod.fst ∘ Subtype.val) h)
  map_rel_iff' := by
    intro x y
    have hPolar : symplecticExtensionB (x.val, (0 : BinaryHyperbolic m)) (y.val, 0) = 0 ↔
        symplecticFour x.val.val y.val.val = 0 := by
      simpa [symplecticExtensionB, hyperbolicB] using
        cast_mod_two_eq_zero (show symplecticFour x.val.val y.val.val < 2 from
          Nat.mod_lt _ (by decide))
    change (_ ∧ symplecticExtensionB (x.val, (0 : BinaryHyperbolic m)) (y.val, 0) = 0) ↔ _
    exact and_congr (not_congr ⟨fun h => Subtype.ext (congrArg (Prod.fst ∘ Subtype.val) h),
      fun h => congrArg _ h⟩) hPolar

end EPPAIII.Primitive
