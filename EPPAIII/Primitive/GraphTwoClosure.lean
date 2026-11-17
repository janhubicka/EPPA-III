import EPPAIII.BlockSystems.SmallHostRankThreeStatement
import EPPAIII.Primitive.LocalSections

/-! # Orbital graphs and the full automorphism group -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

/-- A permutation belongs to the 2-closure when its effect on each ordered
pair is attained by some element of the original subgroup. -/
def permTwoClosure {V : Type*} (P : Subgroup (Equiv.Perm V)) : Subgroup (Equiv.Perm V) where
  carrier := {p | ∀ x y : V, ∃ g : P, g.val x = p x ∧ g.val y = p y}
  one_mem' := fun _ _ => ⟨1, rfl, rfl⟩
  mul_mem' {p q} hp hq := by
    intro x y
    obtain ⟨g, hx, hy⟩ := hq x y
    obtain ⟨f, hqx, hqy⟩ := hp (q x) (q y)
    exact ⟨f * g, by simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hx] using hqx,
      by simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hy] using hqy⟩
  inv_mem' {p} hp := by
    intro x y
    obtain ⟨g, hx, hy⟩ := hp (p.symm x) (p.symm y)
    rw [p.apply_symm_apply] at hx hy
    exact ⟨g⁻¹, g.val.symm_apply_eq.mpr hx.symm, g.val.symm_apply_eq.mpr hy.symm⟩

/-- The three ordered-pair orbits of a subgroup in the graph case. -/
structure HasRankThreeGraphOrbits {V : Type*} (P : Subgroup (Equiv.Perm V))
    (H : SimpleGraph V) : Prop where
  preserves : P ≤ graphAutomorphisms H
  vertices : ∀ x y : V, ∃ p : P, p.val x = y
  pairs : ∀ x y u v : V, x ≠ y → u ≠ v → (H.Adj x y ↔ H.Adj u v) →
    ∃ p : P, p.val x = u ∧ p.val y = v

/-- For a rank-three subgroup in the graph case the full automorphism
group is exactly its 2-closure on the vertex set. -/
theorem permTwoClosure_eq_graphAutomorphisms {V : Type*}
    {P : Subgroup (Equiv.Perm V)} {H : SimpleGraph V}
    (hOrbits : HasRankThreeGraphOrbits P H) : permTwoClosure P = graphAutomorphisms H := by
  apply le_antisymm
  · intro f hf x y
    obtain ⟨g, hx, hy⟩ := hf x y
    have agrees := hOrbits.preserves g.property x y
    simpa only [hx, hy] using agrees
  · intro f hf x y
    by_cases hxy : x = y
    · subst y
      obtain ⟨g, hg⟩ := hOrbits.vertices x (f x)
      exact ⟨g, hg, hg⟩
    · exact hOrbits.pairs x y (f x) (f y) hxy (f.injective.ne hxy) (hf x y)

/-- The full group gives the same orbit interface as a supplied subgroup. -/
theorem HasRankThreeGraphOrbits.of_full {V : Type*} {H : SimpleGraph V}
    (hRank : HasRankThreeAutAction H) : HasRankThreeGraphOrbits (graphAutomorphisms H) H := by
  refine ⟨le_rfl, ?_, ?_⟩
  · intro x y
    obtain ⟨p, hp, hxy⟩ := hRank.2.2.1 x y
    exact ⟨⟨p, hp⟩, hxy⟩
  · intro x y u v hxy huv hAdj
    obtain ⟨p, hp, h₁, h₂⟩ := hRank.2.2.2 x y u v hxy huv hAdj
    exact ⟨⟨p, hp⟩, h₁, h₂⟩

/-- The full graph action inherits rank three from a subgroup with the
three indicated orbits, provided both off-diagonal orbits occur. -/
theorem HasRankThreeGraphOrbits.full_rank_three {V : Type*}
    {P : Subgroup (Equiv.Perm V)} {H : SimpleGraph V} (hOrbits : HasRankThreeGraphOrbits P H)
    (hEdge : ∃ x y, H.Adj x y) (hNonedge : ∃ x y, x ≠ y ∧ ¬ H.Adj x y) :
    HasRankThreeAutAction H := by
  refine ⟨hEdge, hNonedge, ?_, ?_⟩
  · intro x y
    obtain ⟨p, hp⟩ := hOrbits.vertices x y
    exact ⟨p.val, hOrbits.preserves p.property, hp⟩
  · intro x y u v hxy huv hAdj
    obtain ⟨p, hp, hq⟩ := hOrbits.pairs x y u v hxy huv hAdj
    exact ⟨p.val, hOrbits.preserves p.property, hp, hq⟩

/-- A nontrivial graph invariant under the same rank-three subgroup is
one of its two complementary orbital graphs. -/
theorem HasRankThreeGraphOrbits.invariant_graph_eq_or_compl {V : Type*}
    {P : Subgroup (Equiv.Perm V)} {H K : SimpleGraph V} (hOrbits : HasRankThreeGraphOrbits P H)
    (hPreserve : P ≤ graphAutomorphisms K)
    (hHE : ∃ x y, H.Adj x y) (hHN : ∃ x y, x ≠ y ∧ ¬ H.Adj x y)
    (hKE : ∃ x y, K.Adj x y) (hKN : ∃ x y, x ≠ y ∧ ¬ K.Adj x y) :
    H = K ∨ H = Kᶜ := by
  classical
  obtain ⟨a, b, hab⟩ := hHE
  obtain ⟨c, d, hcd, hN⟩ := hHN
  have transfer (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v) (hStatus : H.Adj x y ↔ H.Adj u v) :
      K.Adj x y ↔ K.Adj u v := by
    obtain ⟨p, hx, hy⟩ := hOrbits.pairs x y u v hxy huv hStatus
    simpa only [hx, hy] using (hPreserve p.property x y)
  have onEdge (x y : V) (h : H.Adj x y) : K.Adj x y ↔ K.Adj a b :=
    transfer x y a b h.ne hab.ne (iff_of_true h hab)
  have onNonedge (x y : V) (hne : x ≠ y) (h : ¬ H.Adj x y) : K.Adj x y ↔ K.Adj c d :=
    transfer x y c d hne hcd (iff_of_false h hN)
  by_cases hKeep : K.Adj a b
  · obtain ⟨x, y, hxy, hNot⟩ := hKN
    have hN' : ¬ H.Adj x y := fun h => hNot ((onEdge x y h).mpr hKeep)
    have hDrop : ¬ K.Adj c d := fun h => hNot ((onNonedge x y hxy hN').mpr h)
    left
    ext u v
    by_cases h : H.Adj u v
    · exact iff_of_true h ((onEdge u v h).mpr hKeep)
    · by_cases hne : u = v
      · subst v
        simp
      · exact iff_of_false h (fun hK => hDrop ((onNonedge u v hne h).mp hK))
  · obtain ⟨x, y, hxy⟩ := hKE
    have hN' : ¬ H.Adj x y := fun h => hKeep ((onEdge x y h).mp hxy)
    have hSwitch : K.Adj c d := (onNonedge x y hxy.ne hN').mp hxy
    right
    ext u v
    by_cases h : H.Adj u v
    · exact iff_of_true h ⟨h.ne, fun hK => hKeep ((onEdge u v h).mp hK)⟩
    · by_cases hne : u = v
      · subst v
        simp
      · exact iff_of_false h (fun hK => hK.2 ((onNonedge u v hne h).mpr hSwitch))

end EPPAIII.Primitive
