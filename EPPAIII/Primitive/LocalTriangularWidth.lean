import EPPAIII.Primitive.Triangular
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace EPPAIII.Primitive

/-- A connected non-complete host whose neighbourhoods are triangular
graphs must have underlying width at least four. -/
theorem locallyTriangular_width_ge_four {W : Type*} (H : SimpleGraph W)
    (hConn : H.Preconnected) (hIncomplete : H ≠ ⊤) {m : ℕ}
    (hLocal : ∀ r, Nonempty (H.induce (H.neighborSet r) ≃g triangularGraph (Fin m))) :
    4 ≤ m := by
  classical
  by_contra! hm
  have hComplete (a b : TwoSet (Fin m)) (hne : a ≠ b) :
      (triangularGraph (Fin m)).Adj a b := by
    refine ⟨hne, ?_⟩
    by_contra! hNone
    have hDisjoint : Disjoint a.val b.val :=
      Finset.disjoint_left.mpr hNone
    have hCard : (a.val ∪ b.val).card = 4 := by
      rw [Finset.card_union_of_disjoint hDisjoint, a.property, b.property]
    have hSize := Finset.card_le_univ (a.val ∪ b.val)
    rw [hCard, Fintype.card_fin] at hSize
    omega
  have hCommon (r a b : W) (ha : H.Adj r a) (hb : H.Adj r b) (hne : a ≠ b) :
      H.Adj a b := by
    obtain ⟨iso⟩ := hLocal r
    let a' : H.neighborSet r := ⟨a, ha⟩
    let b' : H.neighborSet r := ⟨b, hb⟩
    have hab : a' ≠ b' := fun h => hne (congrArg Subtype.val h)
    exact iso.map_rel_iff.mp (hComplete (iso a') (iso b') (iso.injective.ne hab))
  have hWalk {a b : W} (walk : H.Walk a b) : a = b ∨ H.Adj a b := by
    induction walk with
    | nil => exact Or.inl rfl
    | @cons a c b hAdj _ ih =>
      rcases ih with rfl | hcb
      · exact Or.inr hAdj
      · by_cases hab : a = b
        · exact Or.inl hab
        · exact Or.inr (hCommon c a b hAdj.symm hcb hab)
  apply hIncomplete
  ext a b
  change H.Adj a b ↔ a ≠ b
  exact ⟨H.ne_of_adj, fun hne => (hWalk (hConn a b).some).resolve_left hne⟩

end EPPAIII.Primitive
