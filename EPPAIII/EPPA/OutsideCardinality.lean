import EPPAIII.EPPA.ProfileOrbitBound

/-!
# The cardinality of the complement of a distinguished induced copy

The finite EPPA orbit bound uses the actual outside vertex set.
For an embedding e : V ↪ W, this set has precisely |W|-|V|
vertices. In particular, a host of order 2st containing sK_t
has exactly st outside vertices; no separate size hypothesis
is mathematically needed.

This elementary result will remove the explicit outside-size
assumption from the final Claim 3.9 Lean statement.
-/

namespace EPPAIII

/-- A finite outside set is the complement of the embedded image. -/
theorem finiteOutside_eq_compl {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq W]
    (e : V ↪ W) :
    finiteOutside e =
      ((Finset.univ : Finset V).image e)ᶜ := by
  classical
  ext w
  simp [finiteOutside, Set.mem_range, Finset.mem_image]

/-- The outside cardinality is |W| minus the size of the embedded
copy, without any regularity or EPPA assumption. -/
theorem finiteOutside_card {V W : Type*}
    [Fintype V] [Fintype W] (e : V ↪ W) :
    (finiteOutside e).card = Fintype.card W - Fintype.card V := by
  classical
  letI : DecidableEq W := Classical.decEq W
  rw [finiteOutside_eq_compl, Finset.card_compl]
  simp [Finset.card_image_of_injective, e.injective]

/-- In a double-size witness for sK_t, the outside has exactly st
vertices. This discharges the size hypothesis in Claim 3.9. -/
theorem finiteOutside_card_clique_union {s t : ℕ}
    {W : Type*} [Fintype W]
    (e : (Fin s × Fin t) ↪ W)
    (hHostSize : Fintype.card W = 2 * s * t) :
    (finiteOutside e).card = s * t := by
  rw [finiteOutside_card]
  simp only [Fintype.card_prod, Fintype.card_fin, hHostSize]
  have hDouble : 2 * s * t = s * t + s * t := by ring
  rw [hDouble]
  omega

end EPPAIII
