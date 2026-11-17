import EPPAIII.Primitive.RookModel
import EPPAIII.DoubleCover.RigidLayerHomogeneity
import Mathlib.Logic.Equiv.Prod

/-!
# Homogeneity of the three-by-three rook graph

A pair of cells admits a coordinate symmetry sending the first cell to
the second while fixing every other cell giving the same adjacency to
the pair. Applying that symmetry one cell at a time extends every
partial automorphism.
-/

namespace EPPAIII.Primitive

open EPPAIII.DoubleCover

private abbrev RookThreeCell := Fin 3 × Fin 3

local instance (x y : RookThreeCell) : Decidable ((rookGraph 3).Adj x y) :=
  inferInstanceAs (Decidable (x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)))

private def coordinateMover (x y : RookThreeCell) : Equiv.Perm RookThreeCell :=
  if x.1 = y.1 then
    Equiv.prodCongr (Equiv.refl _) (Equiv.swap x.2 y.2)
  else if x.2 = y.2 then
    Equiv.prodCongr (Equiv.swap x.1 y.1) (Equiv.refl _)
  else
    let s := Equiv.swap x.2 y.1
    let t := s.trans (Equiv.swap (s y.2) x.1)
    (Equiv.prodComm _ _).trans (Equiv.prodCongr t t.symm)

private theorem coordinateMover_auto (x y : RookThreeCell) :
    IsGraphAutomorphism (rookGraph 3) (coordinateMover x y) := by
  have straight (a b : Equiv.Perm (Fin 3)) (u v : RookThreeCell) :
      (rookGraph 3).Adj u v ↔
        (rookGraph 3).Adj (Equiv.prodCongr a b u) (Equiv.prodCongr a b v) := by
    change (u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2)) ↔
      (Equiv.prodCongr a b u ≠ Equiv.prodCongr a b v ∧
        (a u.1 = a v.1 ∨ b u.2 = b v.2))
    simp only [ne_eq, (Equiv.prodCongr a b).injective.eq_iff, a.injective.eq_iff, b.injective.eq_iff]
  have transpose (u v : RookThreeCell) :
      (rookGraph 3).Adj u v ↔
        (rookGraph 3).Adj (Equiv.prodComm _ _ u) (Equiv.prodComm _ _ v) := by
    change (u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2)) ↔
      (Equiv.prodComm _ _ u ≠ Equiv.prodComm _ _ v ∧ (u.2 = v.2 ∨ u.1 = v.1))
    simp only [ne_eq, (Equiv.prodComm (Fin 3) (Fin 3)).injective.eq_iff, or_comm]
  intro u v
  unfold coordinateMover
  split
  · exact straight _ _ u v
  · split
    · exact straight _ _ u v
    · exact (transpose u v).trans (straight _ _ _ _)

set_option maxHeartbeats 4000000 in
private theorem coordinateMover_apply :
    ∀ x y : RookThreeCell, coordinateMover x y x = y := by decide

set_option maxHeartbeats 4000000 in
private theorem coordinateMover_fix :
    ∀ x y z : RookThreeCell, z ≠ x → z ≠ y →
      ((rookGraph 3).Adj x z ↔ (rookGraph 3).Adj y z) → coordinateMover x y z = z := by
  decide

/-- Every partial automorphism of the three-by-three rook graph extends. -/
theorem rookThree_homogeneous : IsHomogeneousGraph (rookGraph 3) := by
  intro D
  induction D using Finset.induction_on with
  | empty =>
      intro p _
      exact ⟨Equiv.refl _, fun _ _ => Iff.rfl, by simp⟩
  | @insert x D hx ih =>
      intro p hp
      have hpD : IsPartialGraphAutomorphism (rookGraph 3) D p := by
        intro u v hu hv
        exact hp u v (Finset.mem_insert_of_mem hu) (Finset.mem_insert_of_mem hv)
      obtain ⟨q, hq, hAgree⟩ := ih p hpD
      let r := coordinateMover (q x) (p x)
      have hr := coordinateMover_auto (q x) (p x)
      refine ⟨q.trans r, fun u v => (hq u v).trans (hr (q u) (q v)), ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact coordinateMover_apply (q v) (p v)
      · change r (q v) = p v
        rw [← hAgree v hv]
        have hqv : q v ≠ q x := fun h => hx (q.injective h ▸ hv)
        have hpv : q v ≠ p x := by
          rw [hAgree v hv]
          exact fun h => hx (p.injective h ▸ hv)
        have hAdj : (rookGraph 3).Adj (q x) (q v) ↔
            (rookGraph 3).Adj (p x) (q v) := by
          calc
            (rookGraph 3).Adj (q x) (q v) ↔ (rookGraph 3).Adj x v := (hq x v).symm
            _ ↔ (rookGraph 3).Adj (p x) (p v) :=
              hp x v (Finset.mem_insert_self x D) (Finset.mem_insert_of_mem hv)
            _ ↔ (rookGraph 3).Adj (p x) (q v) := by rw [hAgree v hv]
        exact coordinateMover_fix (q x) (p x) (q v) hqv hpv hAdj

end EPPAIII.Primitive
