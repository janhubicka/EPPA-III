import EPPAIII.EPPA.ProfileOrbitBound
import EPPAIII.CliqueCovers.Basic

/-!
# Explicit generators of Aut(sK_t)

A permutation of clique indices, and independent permutations within
each clique, are genuine automorphisms of the disjoint clique union.
Their translated neighbourhood profiles therefore occur in the
finite EPPA profile orbit. No complementary clique stabilizer
or outside regularity is assumed.
-/

namespace EPPAIII.CliqueCovers

/-- Relabel clique indices but not within-clique coordinates. -/
def outerPermutation {s t : ℕ} (p : Equiv.Perm (Fin s)) :
    Equiv.Perm (Fin s × Fin t) where
  toFun := fun x => (p x.1, x.2)
  invFun := fun x => (p.symm x.1, x.2)
  left_inv := by
    intro x
    rcases x with ⟨i,a⟩
    simp
  right_inv := by
    intro x
    rcases x with ⟨i,a⟩
    simp

theorem outerPermutation_aut {s t : ℕ}
    (p : Equiv.Perm (Fin s)) :
    IsGraphAutomorphism (cliqueUnion s t) (outerPermutation p) := by
  intro x y
  change (x.1 = y.1 ∧ x.2 ≠ y.2) ↔
    (p x.1 = p y.1 ∧ x.2 ≠ y.2)
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨congrArg p h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨p.injective h, h'⟩

/-- Relabel each clique independently, preserving its index. -/
def innerPermutation {s t : ℕ}
    (p : Fin s → Equiv.Perm (Fin t)) :
    Equiv.Perm (Fin s × Fin t) where
  toFun := fun x => (x.1, p x.1 x.2)
  invFun := fun x => (x.1, (p x.1).symm x.2)
  left_inv := by
    intro x
    rcases x with ⟨i,a⟩
    simp
  right_inv := by
    intro x
    rcases x with ⟨i,a⟩
    simp

theorem innerPermutation_aut {s t : ℕ}
    (p : Fin s → Equiv.Perm (Fin t)) :
    IsGraphAutomorphism (cliqueUnion s t) (innerPermutation p) := by
  intro x y
  change (x.1 = y.1 ∧ x.2 ≠ y.2) ↔
    (x.1 = y.1 ∧ p x.1 x.2 ≠ p y.1 y.2)
  by_cases hij : x.1 = y.1
  · rw [← hij]
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h, (p x.1).injective.ne h'⟩
    · rintro ⟨h, h'⟩
      exact ⟨h, fun eq => h' (congrArg (p x.1) eq)⟩
  · simp [hij]

/-- A base automorphism contributes its translated profile to
the full finite profile orbit. -/
theorem translate_in_finite_profile_orbit {V W : Type*}
    [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (w : W) (p : Equiv.Perm V)
    (hp : IsGraphAutomorphism G p) :
    translatedFiniteProfile H e w p ∈ finiteProfileOrbit G H e w := by
  classical
  unfold finiteProfileOrbit
  apply Finset.mem_image.mpr
  refine ⟨p, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩

/-- Clique-index relabellings contribute to the finite orbit. -/
theorem outer_profile_in_orbit {s t : ℕ} {W : Type*}
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (w : W) (p : Equiv.Perm (Fin s)) :
    translatedFiniteProfile H e w (outerPermutation p) ∈
      finiteProfileOrbit (cliqueUnion s t) H e w :=
  translate_in_finite_profile_orbit
    (cliqueUnion s t) H e w (outerPermutation p)
    (outerPermutation_aut p)

/-- Independent within-clique relabellings contribute to the orbit. -/
theorem inner_profile_in_orbit {s t : ℕ} {W : Type*}
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (w : W) (p : Fin s → Equiv.Perm (Fin t)) :
    translatedFiniteProfile H e w (innerPermutation p) ∈
      finiteProfileOrbit (cliqueUnion s t) H e w :=
  translate_in_finite_profile_orbit
    (cliqueUnion s t) H e w (innerPermutation p)
    (innerPermutation_aut p)

end EPPAIII.CliqueCovers
