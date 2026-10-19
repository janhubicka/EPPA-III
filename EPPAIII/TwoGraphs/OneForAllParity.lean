import EPPAIII.TwoGraphs.TaylorFibresDistance

/-!
# Elementary parity checks for the Section 5 one-for-all argument

These lemmas isolate the Boolean arithmetic in `lem:separation`
and `prop:one-for-all`. They do not assume homogeneity, EPPA, or any
lift from two-graph automorphisms to host automorphisms. Those global
group-action interfaces remain separate validation obligations.
-/

namespace EPPAIII.TwoGraphs

/-- If the XOR discrepancy between two neighbourhood functions
has zero difference on every pair, then the functions are
everywhere equal or everywhere complementary. The empty set is
also covered. -/
theorem types_equal_or_complementary {R : Type*}
    (ea eb : R → Bool)
    (hParity : ∀ r s : R,
      Bool.xor (ea r) (ea s) =
        Bool.xor (eb r) (eb s)) :
    (∀ r : R, ea r = eb r) ∨
      (∀ r : R, ea r ≠ eb r) := by
  by_cases hR : Nonempty R
  · obtain ⟨r₀⟩ := hR
    by_cases heq : ea r₀ = eb r₀
    · left
      intro r
      have hp := hParity r r₀
      cases ha : ea r <;> cases hb : eb r <;>
        cases har : ea r₀ <;> cases hbr : eb r₀ <;>
        simp_all [Bool.xor]
    · right
      intro r
      have hp := hParity r r₀
      cases ha : ea r <;> cases hb : eb r <;>
        cases har : ea r₀ <;> cases hbr : eb r₀ <;>
        simp_all [Bool.xor]
  · left
    intro r
    exact (hR ⟨r⟩).elim

/-- If a switching set separates two base points, at least one
of a transversal and its switch separates those points. -/
theorem one_of_two_switchings_separates {X : Type*}
    (c switch : X → Bool) (a b : X)
    (hSep : switch a ≠ switch b) :
    c a ≠ c b ∨
      Bool.xor (c a) (switch a) ≠
        Bool.xor (c b) (switch b) := by
  cases ha : c a <;> cases hb : c b <;>
    cases hsa : switch a <;> cases hsb : switch b <;>
    simp_all [Bool.xor]

/-- Complementary neighbourhood types become equal after a
switching that separates the two distinguished vertices.
The switching choice at a third vertex cancels on both sides. -/
theorem complementary_types_equal_after_switch
    (ea eb ta tb tr : Bool)
    (hTypes : ea ≠ eb) (hSep : ta ≠ tb) :
    Bool.xor (Bool.xor ea ta) tr =
      Bool.xor (Bool.xor eb tb) tr := by
  cases ea <;> cases eb <;>
    cases ta <;> cases tb <;> cases tr <;>
    simp_all [Bool.xor]

/-- The previous identity simultaneously holds at every vertex
in the fixed part of a partial automorphism. -/
theorem complementary_types_equal_after_switch_on {R : Type*}
    (ea eb tr : R → Bool) (ta tb : Bool)
    (hTypes : ∀ r : R, ea r ≠ eb r)
    (hSep : ta ≠ tb) :
    ∀ r : R,
      Bool.xor (Bool.xor (ea r) ta) (tr r) =
        Bool.xor (Bool.xor (eb r) tb) (tr r) := by
  intro r
  exact complementary_types_equal_after_switch
    (ea r) (eb r) ta tb (tr r) (hTypes r) hSep

end EPPAIII.TwoGraphs
