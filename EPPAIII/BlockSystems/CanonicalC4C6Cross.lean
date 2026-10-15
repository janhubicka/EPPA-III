import Mathlib

/-!
# Canonical 4-cycle plus 6-cycle cross incidence on five plus five points

This is the finite graph computation behind the omitted alternative
in Lemma 3.18. The first two bottom vertices and first two top
vertices span K_{2,2}=C4. The remaining three vertices on each
side form a bipartite C6, with the six prescribed edges.

All vertices on both sides have cross degree exactly two. Exactly
one unordered pair of distinct bottom vertices has two common
top neighbours, namely {0,1}. These are proved by kernel-checked
finite computation in Lean, not by an external enumeration.

A separate orbit argument transfers this certificate to an EPPA
host after identifying its cross-incidence matrix with this
canonical model.
-/

namespace EPPAIII.BlockSystems

/-- The C4 ⊔ C6 cross relation between two five-vertex layers. -/
def canonicalC4C6Cross (x z : Fin 5) : Prop :=
  (x.val < 2 ∧ z.val < 2) ∨
  (x.val = 2 ∧ (z.val = 2 ∨ z.val = 3)) ∨
  (x.val = 3 ∧ (z.val = 3 ∨ z.val = 4)) ∨
  (x.val = 4 ∧ (z.val = 4 ∨ z.val = 2))

/-- The number of common top neighbours of two bottom vertices
in the canonical bipartite cross relation. -/
def canonicalC4C6CommonCount (x y : Fin 5) : ℕ :=
  ((Finset.univ : Finset (Fin 5)).filter
    (fun z => canonicalC4C6Cross x z ∧
      canonicalC4C6Cross y z)).card

/-- Both parts of the canonical 4+6 cross relation have degree two. -/
theorem canonicalC4C6_cross_regular :
    (∀ x : Fin 5,
      ((Finset.univ : Finset (Fin 5)).filter
        (fun z => canonicalC4C6Cross x z)).card = 2) ∧
    (∀ z : Fin 5,
      ((Finset.univ : Finset (Fin 5)).filter
        (fun x => canonicalC4C6Cross x z)).card = 2) := by
  decide

/-- Its C4 is separated from the remaining six vertices:
all cross edges join either indices below two on both sides,
or indices at least two on both sides. -/
theorem canonicalC4C6_component_separation :
    ∀ x z : Fin 5, canonicalC4C6Cross x z →
      (x.val < 2 ↔ z.val < 2) := by
  decide

/-- The C4 component determines the unique unordered pair of
distinct base vertices having two common outside neighbours. -/
theorem canonicalC4C6_unique_double_common_pair :
    ∀ x y : Fin 5, x ≠ y →
      (canonicalC4C6CommonCount x y = 2 ↔
        ({x,y} : Finset (Fin 5)) = {0,1}) := by
  decide

end EPPAIII.BlockSystems
