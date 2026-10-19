import EPPAIII.TwoGraphs.PartialAutomorphismParity
import EPPAIII.TwoGraphs.TaylorFibresDistance

/-!
# A direct Boolean switching potential for two-graph automorphisms

The XOR discrepancy of a graph and its relabelling is a coboundary
whenever the triangle parity agrees. This avoids invoking the
Mallows--Sloane theorem just to lift a full two-graph automorphism.
All assertions are independent of finiteness.
-/

namespace EPPAIII.TwoGraphs

/-- Six Boolean summands cancel when their triple parities agree. -/
theorem xor_three_pairs_zero (a b c d e f : Bool)
    (h : Bool.xor (Bool.xor a b) c =
         Bool.xor (Bool.xor d e) f) :
    Bool.xor (Bool.xor (Bool.xor a d) (Bool.xor b e))
      (Bool.xor c f) = false := by
  cases a <;> cases b <;> cases c <;>
    cases d <;> cases e <;> cases f <;> simp_all [Bool.xor]

/-- A symmetric Boolean two-point discrepancy whose parity vanishes
on every triple has an anchored switching potential. -/
theorem xor_triangle_potential
    {V : Type*} (delta : V → V → Bool)
    (hSym : ∀ x y, delta x y = delta y x)
    (hTriangle : ∀ x y z,
      Bool.xor (Bool.xor (delta x y) (delta y z))
        (delta z x) = false) :
    ∃ h : V → Bool, ∀ x y,
      delta x y = Bool.xor (h x) (h y) := by
  classical
  by_cases hNonempty : Nonempty V
  · obtain ⟨r⟩ := hNonempty
    refine ⟨fun x => delta r x, ?_⟩
    intro x y
    have ht := hTriangle r x y
    rw [hSym y r] at ht
    cases hrx : delta r x <;>
      cases hxy : delta x y <;>
      cases hry : delta r y <;>
      simp_all [Bool.xor]
  · refine ⟨fun _ => false, ?_⟩
    intro x y
    exact (hNonempty ⟨x⟩).elim

/-- A relabelling which preserves the parity of every base triple
produces a switching potential for its edge discrepancy. -/
theorem xor_potential_of_triple_parity
    {V : Type*}
    (edge : V → V → Bool)
    (hSym : ∀ x y, edge x y = edge y x)
    (f : Equiv.Perm V)
    (hTriple : ∀ x y z,
      Bool.xor (Bool.xor (edge x y) (edge y z))
        (edge z x) =
      Bool.xor (Bool.xor (edge (f x) (f y))
        (edge (f y) (f z))) (edge (f z) (f x))) :
    ∃ h : V → Bool, ∀ x y,
      Bool.xor (edge x y) (edge (f x) (f y)) =
        Bool.xor (h x) (h y) := by
  let delta : V → V → Bool := fun x y =>
    Bool.xor (edge x y) (edge (f x) (f y))
  have hDeltaSym : ∀ x y, delta x y = delta y x := by
    intro x y
    change Bool.xor (edge x y) (edge (f x) (f y)) =
      Bool.xor (edge y x) (edge (f y) (f x))
    rw [hSym x y, hSym (f x) (f y)]
  have hDeltaTriangle : ∀ x y z,
      Bool.xor (Bool.xor (delta x y) (delta y z))
        (delta z x) = false := by
    intro x y z
    exact xor_three_pairs_zero
      (edge x y) (edge y z) (edge z x)
      (edge (f x) (f y)) (edge (f y) (f z))
      (edge (f z) (f x)) (hTriple x y z)
  exact xor_triangle_potential delta hDeltaSym hDeltaTriangle

end EPPAIII.TwoGraphs
