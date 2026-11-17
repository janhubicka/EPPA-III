import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Square rook graphs -/

namespace EPPAIII.Primitive

/-- The rook graph on an n-by-n lattice. -/
def rookGraph (n : ℕ) : SimpleGraph (Fin n × Fin n) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.elim (fun h => .inl h.symm) (fun h => .inr h.symm)⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

end EPPAIII.Primitive
