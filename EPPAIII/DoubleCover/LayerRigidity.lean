import Mathlib

/-!
# Rigidity of the layers of an invariant two-point fibre system

This isolates the group-theoretic step used to exclude the
one-edge and three-edge configurations in Section 3. The
"exceptional relation" can be the unique edge or unique
nonedge between two fibres. If it is invariant, always joins
vertices on the same layer, and occurs between every pair of
distinct fibres, then a fibre-preserving automorphism cannot
change the layer on only some fibres.

This theorem does not assume anything about the particular graph
producing the exceptional relation. Instantiating it with
the explicit one-edge/three-edge matrices is the remaining bridge.
-/

namespace EPPAIII.DoubleCover

/-- A permutation taking each pair into one pair has opposite first
coordinates on the images of its two fibre mates. -/
theorem fibre_layer_complement {V : Type*}
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hFibre : ∀ (b : Bool) (x : V), (q (b, x)).2 = σ x)
    (x : V) :
    (q (true, x)).1 = !(q (false, x)).1 := by
  have hne : (q (true, x)).1 ≠ (q (false, x)).1 := by
    intro hfirst
    have hsecond : (q (true, x)).2 = (q (false, x)).2 := by
      simpa [hFibre]
    have hp : q (true, x) = q (false, x) := Prod.ext hfirst hsecond
    have he : (true, x) = (false, x) := q.injective hp
    cases he
  cases hf : (q (false, x)).1 <;> cases ht : (q (true, x)).1 <;>
    simp_all

/-- The exceptional pair relation forces every fibre to have the same
flip status under a fibre-preserving automorphism. -/
theorem uniform_layer_of_exceptional {V : Type*}
    (R : (Bool × V) → (Bool × V) → Prop)
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hFibre : ∀ (b : Bool) (x : V), (q (b, x)).2 = σ x)
    (hPreserve : ∀ u v, R u v ↔ R (q u) (q v))
    (hExists : ∀ x y : V, x ≠ y → ∃ b : Bool, R (b, x) (b, y))
    (hSame : ∀ u v, R u v → u.1 = v.1) :
    ∀ x y : V, (q (false, x)).1 = (q (false, y)).1 := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  obtain ⟨b, hb⟩ := hExists x y hxy
  have hs : (q (b, x)).1 = (q (b, y)).1 :=
    hSame _ _ ((hPreserve _ _).mp hb)
  cases b with
  | false => exact hs
  | true =>
      have hx := fibre_layer_complement q σ hFibre x
      have hy := fibre_layer_complement q σ hFibre y
      rw [hx, hy] at hs
      cases hfx : (q (false, x)).1 <;>
        cases hfy : (q (false, y)).1 <;> simp_all

/-- If one selected vertex stays in the bottom layer, then every
selected vertex stays in the bottom layer. -/
theorem all_bottom_of_one_bottom {V : Type*}
    (R : (Bool × V) → (Bool × V) → Prop)
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hFibre : ∀ (b : Bool) (x : V), (q (b, x)).2 = σ x)
    (hPreserve : ∀ u v, R u v ↔ R (q u) (q v))
    (hExists : ∀ x y : V, x ≠ y → ∃ b : Bool, R (b, x) (b, y))
    (hSame : ∀ u v, R u v → u.1 = v.1)
    (x0 : V) (hx0 : (q (false, x0)).1 = false) :
    ∀ x : V, (q (false, x)).1 = false := by
  intro x
  calc
    (q (false, x)).1 = (q (false, x0)).1 :=
      uniform_layer_of_exceptional R q σ hFibre
        hPreserve hExists hSame x x0
    _ = false := hx0

end EPPAIII.DoubleCover
