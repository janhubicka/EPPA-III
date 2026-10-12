import EPPAIII.CliqueCovers.Claim39OrbitBridge
import EPPAIII.DoubleCover.TwoPointAction

/-!
# The two pair orbits of the natural wreath action on s blocks of t points

This is the purely group-theoretic part of the one-partial-profile
classification in Lemma 3.7. The natural S_t wr S_s action on
Fin s × Fin t is transitive on ordered distinct pairs sharing a
clique index and, separately, on ordered pairs with distinct indices.

It follows that every simple graph invariant under this action has
constant adjacency on same-block pairs and on different-block pairs.
No assumption about EPPA witnesses or complementary cliques appears
here; transferring the canonical outside action to this model is
the next graph-level obligation.
-/

namespace EPPAIII.CliqueCovers

/-- Any two ordered pairs from distinct coordinate blocks can
be mapped to each other by a genuine wreath-product permutation. -/
theorem wreath_maps_cross_block_pair {s t : ℕ}
    (x y u v : Fin s × Fin t)
    (hxy : x.1 ≠ y.1) (huv : u.1 ≠ v.1) :
    ∃ outer : Equiv.Perm (Fin s),
      ∃ inner : Fin s → Equiv.Perm (Fin t),
        ((outerPermutation outer).trans (innerPermutation inner)) x = u ∧
        ((outerPermutation outer).trans (innerPermutation inner)) y = v := by
  classical
  obtain ⟨outer,hx,hy⟩ :=
    EPPAIII.DoubleCover.exists_perm_of_two_maps
      x.1 y.1 u.1 v.1 hxy huv
  let inner : Fin s → Equiv.Perm (Fin t) :=
    fun j => if j = u.1 then Equiv.swap x.2 u.2
      else if j = v.1 then Equiv.swap y.2 v.2 else Equiv.refl _
  refine ⟨outer, inner, ?_, ?_⟩
  · change (outer x.1, inner (outer x.1) x.2) = (u.1,u.2)
    simp [hx, inner]
  · change (outer y.1, inner (outer y.1) y.2) = (v.1,v.2)
    simp [hy, inner, huv.symm]

/-- Any two ordered distinct pairs within one block can
be mapped to each other by a genuine wreath-product permutation. -/
theorem wreath_maps_same_block_pair {s t : ℕ}
    (x y u v : Fin s × Fin t)
    (hxy : x ≠ y) (huv : u ≠ v)
    (hx : x.1 = y.1) (hu : u.1 = v.1) :
    ∃ outer : Equiv.Perm (Fin s),
      ∃ inner : Fin s → Equiv.Perm (Fin t),
        ((outerPermutation outer).trans (innerPermutation inner)) x = u ∧
        ((outerPermutation outer).trans (innerPermutation inner)) y = v := by
  classical
  have hxy2 : x.2 ≠ y.2 := by
    intro he
    exact hxy (Prod.ext hx he)
  have huv2 : u.2 ≠ v.2 := by
    intro he
    exact huv (Prod.ext hu he)
  obtain ⟨inner0,hx2,hy2⟩ :=
    EPPAIII.DoubleCover.exists_perm_of_two_maps
      x.2 y.2 u.2 v.2 hxy2 huv2
  let outer : Equiv.Perm (Fin s) := Equiv.swap x.1 u.1
  let inner : Fin s → Equiv.Perm (Fin t) :=
    fun j => if j = u.1 then inner0 else Equiv.refl _
  refine ⟨outer,inner,?_,?_⟩
  · change (outer x.1, inner (outer x.1) x.2) = (u.1,u.2)
    simp [outer, inner, hx2]
  · change (outer y.1, inner (outer y.1) y.2) = (v.1,v.2)
    simp [outer, inner, ← hx, ← hu, hy2]

/-- There are exactly two orbits on ordered distinct pairs:
within-block and between-block pairs. -/
theorem exists_wreath_maps_pair_of_same_block_status {s t : ℕ}
    (x y u v : Fin s × Fin t)
    (hxy : x ≠ y) (huv : u ≠ v)
    (hStatus : (x.1 = y.1) ↔ (u.1 = v.1)) :
    ∃ outer : Equiv.Perm (Fin s),
      ∃ inner : Fin s → Equiv.Perm (Fin t),
        ((outerPermutation outer).trans (innerPermutation inner)) x = u ∧
        ((outerPermutation outer).trans (innerPermutation inner)) y = v := by
  by_cases hx : x.1 = y.1
  · exact wreath_maps_same_block_pair x y u v hxy huv hx (hStatus.mp hx)
  · have hu : u.1 ≠ v.1 := by
      intro hu
      exact hx (hStatus.mpr hu)
    exact wreath_maps_cross_block_pair x y u v hx hu

/-- Every graph invariant under the natural wreath action has
one uniform adjacency value on within-block unordered pairs and
one uniform value on between-block unordered pairs. -/
theorem wreath_invariant_graph_pair_uniform {s t : ℕ}
    (B : SimpleGraph (Fin s × Fin t))
    (hInvariant : ∀ (outer : Equiv.Perm (Fin s))
      (inner : Fin s → Equiv.Perm (Fin t)),
      IsGraphAutomorphism B
        ((outerPermutation outer).trans (innerPermutation inner)))
    (x y u v : Fin s × Fin t)
    (hxy : x ≠ y) (huv : u ≠ v)
    (hStatus : (x.1 = y.1) ↔ (u.1 = v.1)) :
    B.Adj x y ↔ B.Adj u v := by
  obtain ⟨outer,inner,hx,hy⟩ :=
    exists_wreath_maps_pair_of_same_block_status
      x y u v hxy huv hStatus
  simpa [hx,hy] using (hInvariant outer inner x y)

end EPPAIII.CliqueCovers
