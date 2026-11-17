import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Equal-part bipartition graphs -/

namespace EPPAIII.Primitive

/-- Represent an unordered partition into two equal parts by the
unique part containing 0. Each part has size m+1. -/
abbrev EqualBipartitionVertex (m : ℕ) :=
  {s : Finset (Fin (2 * (m + 1))) //
    s.card = m + 1 ∧ (⟨0, by omega⟩ : Fin (2 * (m + 1))) ∈ s}

/-- Two bipartitions are adjacent if some parts meet in exactly one
point. For m=3 and m=4 this gives the 35- and 126-vertex graphs from
Brouwer–Van Maldeghem Theorem 11.3.1 (iii) and (iv). -/
def equalBipartitionGraph (m : ℕ) :
    SimpleGraph (EqualBipartitionVertex m) where
  Adj x y := x ≠ y ∧ ((x.val ∩ y.val).card = 1 ∨ (x.val ∩ y.val).card = m)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

instance (m : ℕ) : DecidableRel (equalBipartitionGraph m).Adj := fun a b => by
  change Decidable (a ≠ b ∧ ((a.val ∩ b.val).card = 1 ∨ (a.val ∩ b.val).card = m))
  infer_instance

end EPPAIII.Primitive
