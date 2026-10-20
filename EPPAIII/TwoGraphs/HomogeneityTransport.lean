import EPPAIII.DoubleCover.RigidLayerHomogeneity

/-!
# Homogeneity transport across graph equivalences

A finite graph's partial-automorphism extension property on its
*own vertex set* is invariant under renaming the vertices. This
is the generic interface required to transport the existing
cliqueUnion_isHomogeneous theorem to an arbitrary selected
graph decomposed into equal-sized true-twin classes.

The proof explicitly conjugates partial maps and full automorphisms.
No graph classification or EPPA witness is assumed.
-/

namespace EPPAIII.TwoGraphs

/-- If G is homogeneous, so is its pullback through any
equivalence of vertex types. No finiteness assumption is needed
beyond the finite domains represented by Finset. -/
theorem homogeneous_comap_equiv
    {V W : Type*}
    (G : SimpleGraph W) (φ : V ≃ W)
    (hHom : EPPAIII.DoubleCover.IsHomogeneousGraph G) :
    EPPAIII.DoubleCover.IsHomogeneousGraph (G.comap φ) := by
  classical
  intro D p hPartial
  let q : Equiv.Perm W :=
    (φ.symm.trans p).trans φ
  have hPartialW :
      IsPartialGraphAutomorphism G (D.image φ) q := by
    intro a b ha hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    have hp := hPartial x y hx hy
    change G.Adj (φ x) (φ y) ↔
      G.Adj (φ (p x)) (φ (p y)) at hp
    simpa [q] using hp
  obtain ⟨σ,hσ,hExt⟩ :=
    hHom (D.image φ) q hPartialW
  let τ : Equiv.Perm V :=
    (φ.trans σ).trans φ.symm
  refine ⟨τ,?_,?_⟩
  · intro x y
    have hh := hσ (φ x) (φ y)
    simpa [τ] using hh
  · intro x hx
    have hh := hExt (φ x)
      (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    apply φ.injective
    simpa [τ, q] using hh

end EPPAIII.TwoGraphs
