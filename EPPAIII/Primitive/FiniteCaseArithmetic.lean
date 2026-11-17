import Lean.Elab.Tactic.Omega

/-! # Arithmetic used in the small sporadic cases of Section 8 -/

namespace EPPAIII.Primitive

/-- The two equations for a putative rank-three second constituent of
`M₂₂` force its nonneighbor common-neighbor count to vanish. -/
theorem m22_nonlocal_mu_eq_zero (l m : Nat)
    (hl : l ≤ 11) (hParameters : 47 * m = 12 * (11 - l)) : m = 0 := by
  omega

/-- A nine-vertex selection from six triangles is counted by its full
triangles, isolated edges, and singletons. The three excluded induced
profiles leave the three possibilities used in the proof. -/
theorem gqThreeFive_nine_vertex_profiles (a b c : Nat)
    (hComponents : a + b + c ≤ 6) (hNine : 3 * a + 2 * b + c = 9)
    (hNoFourEdges : a + b < 4)
    (hNoThreeEdgesTwoSingletons : a + b < 3 ∨ a + b + c < 5)
    (hNoThreeTriangles : a < 3) :
    (a = 2 ∧ b = 1 ∧ c = 1) ∨ (a = 2 ∧ b = 0 ∧ c = 3) ∨
      (a = 1 ∧ b = 1 ∧ c = 4) := by
  omega

/-- The three surviving nine-vertex profiles force section orders that
cannot divide the corresponding point or pair stabilizer orders. -/
theorem gqThreeFive_section_orders :
    ¬ 48 ∣ (120 : Nat) ∧ ¬ 144 ∣ (120 : Nat) ∧ ¬ 288 ∣ (2160 : Nat) := by
  decide

/-- Three edges at most and an independent set of at most seven vertices
put the selected second constituent strictly above half its order. -/
theorem bvls_nonlocal_above_half (a b n₂ : Nat)
    (hEdges : a ≤ 3) (hIndependent : a + b ≤ 7)
    (hSize : 243 ≤ 2 * (1 + (2 * a + b) + n₂)) : 220 < 2 * n₂ := by
  omega

/-- The parameter equality of a putative rank-three second constituent
of the Berlekamp–Van Lint–Seidel graph forces no common neighbors of a nonedge. -/
theorem bvls_nonlocal_mu_eq_zero (l m : Nat)
    (hl : l ≤ 19) (hParameters : 199 * m = 20 * (19 - l)) : m = 0 := by
  omega

end EPPAIII.Primitive
