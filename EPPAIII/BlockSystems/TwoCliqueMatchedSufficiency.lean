import EPPAIII.BlockSystems.ImprimitiveSufficiencyLifts
import EPPAIII.BlockSystems.TwoCliqueTaylorNamed

/-!
# Genuine sufficiency for the unequal two-clique EPPA witnesses

The two original clique components may have *unequal* sizes.  It would
therefore be incorrect to use homogeneity of the selected base.

Instead an arbitrary permutation of the base index set extends to an
automorphism of the two host cliques by an XOR adjustment of the side
bit.  A *partial* base automorphism has constant color discrepancy on
its domain, so this host automorphism agrees with the actual selected
copy there. Both values of the optional mate-matching bit are covered.
-/

namespace EPPAIII.BlockSystems

open EPPAIII.DoubleCover

/-- Host symmetry indexed by *any* vertex permutation and a global
choice of whether to swap the two host clique components. -/
def twoCliqueMatchedSymmetry
    {V : Type*} (c : V → Bool)
    (p : Equiv.Perm V) (delta : Bool) :
    Equiv.Perm (Bool × V) where
  toFun := fun u =>
    (Bool.xor (Bool.xor (Bool.xor u.1 (c u.2)) (c (p u.2))) delta,
     p u.2)
  invFun := fun u =>
    (Bool.xor (Bool.xor (Bool.xor u.1 (c u.2))
        (c (p.symm u.2))) delta,
     p.symm u.2)
  left_inv := by
    rintro ⟨b,x⟩
    apply Prod.ext
    · change Bool.xor
        (Bool.xor
          (Bool.xor
            (Bool.xor
              (Bool.xor (Bool.xor b (c x)) (c (p x))) delta)
            (c (p x))) (c (p.symm (p x)))) delta = b
      rw [p.symm_apply_apply]
      cases b <;> cases hc : c x <;>
        cases hcp : c (p x) <;> cases delta <;>
        simp [hc, hcp, Bool.xor]
    · simp
  right_inv := by
    rintro ⟨b,x⟩
    apply Prod.ext
    · change Bool.xor
        (Bool.xor
          (Bool.xor
            (Bool.xor
              (Bool.xor (Bool.xor b (c x)) (c (p.symm x))) delta)
            (c (p.symm x))) (c (p (p.symm x)))) delta = b
      rw [p.apply_symm_apply]
      cases b <;> cases hc : c x <;>
        cases hcp : c (p.symm x) <;> cases delta <;>
        simp [hc, hcp, Bool.xor]
    · simp

/-- The *global* host clique label changes by the single bit delta. -/
theorem twoCliqueMatchedSymmetry_label
    {V : Type*} (c : V → Bool)
    (p : Equiv.Perm V) (delta : Bool)
    (u : Bool × V) :
    Bool.xor (twoCliqueMatchedSymmetry c p delta u).1
      (c (twoCliqueMatchedSymmetry c p delta u).2) =
      Bool.xor (Bool.xor u.1 (c u.2)) delta := by
  rcases u with ⟨b,x⟩
  change Bool.xor
      (Bool.xor (Bool.xor (Bool.xor b (c x)) (c (p x))) delta)
      (c (p x)) =
    Bool.xor (Bool.xor b (c x)) delta
  cases b <;> cases hc : c x <;>
    cases hcp : c (p x) <;> cases delta <;>
    simp [hc, hcp, Bool.xor]

/-- Neither the two host cliques nor its mate matching is disturbed. -/
theorem twoCliqueMatchedSymmetry_graphAut
    {V : Type*} (c : V → Bool) (mate : Bool)
    (p : Equiv.Perm V) (delta : Bool) :
    IsGraphAutomorphism (twoCliqueMatchedGraph c mate)
      (twoCliqueMatchedSymmetry c p delta) := by
  let q := twoCliqueMatchedSymmetry c p delta
  have hxorCancel (a b d : Bool)
      (h : Bool.xor a d = Bool.xor b d) : a = b := by
    cases a <;> cases b <;> cases d <;>
      simp_all [Bool.xor]
  intro u v
  change
    (u ≠ v ∧
      (Bool.xor u.1 (c u.2) = Bool.xor v.1 (c v.2) ∨
       (mate = true ∧ u.2 = v.2))) ↔
    (q u ≠ q v ∧
      (Bool.xor (q u).1 (c (q u).2) =
         Bool.xor (q v).1 (c (q v).2) ∨
       (mate = true ∧ (q u).2 = (q v).2)))
  constructor
  · rintro ⟨huv, hStatus⟩
    refine ⟨q.injective.ne huv, ?_⟩
    rcases hStatus with hColor | ⟨hmate, hSame⟩
    · left
      rw [show Bool.xor (q u).1 (c (q u).2) =
          Bool.xor (Bool.xor u.1 (c u.2)) delta from
          twoCliqueMatchedSymmetry_label c p delta u,
          show Bool.xor (q v).1 (c (q v).2) =
          Bool.xor (Bool.xor v.1 (c v.2)) delta from
          twoCliqueMatchedSymmetry_label c p delta v]
      exact congrArg (fun b => Bool.xor b delta) hColor
    · right
      refine ⟨hmate, ?_⟩
      change p u.2 = p v.2
      exact congrArg p hSame
  · rintro ⟨huv, hStatus⟩
    refine ⟨(fun h => huv (congrArg q h)), ?_⟩
    rcases hStatus with hColor | ⟨hmate, hSame⟩
    · left
      rw [twoCliqueMatchedSymmetry_label c p delta u,
          twoCliqueMatchedSymmetry_label c p delta v] at hColor
      exact hxorCancel _ _ _ hColor
    · right
      refine ⟨hmate, ?_⟩
      change p u.2 = p v.2 at hSame
      exact p.injective hSame

/-- Every partial automorphism of a two-clique graph has a single
Boolean discrepancy between source and target clique colors. -/
theorem twoClique_partial_color_discrepancy
    {V : Type*}
    (c : V → Bool)
    (D : Finset V) (p : Equiv.Perm V)
    (hp : IsPartialGraphAutomorphism (twoCliqueGraph c) D p)
    (x y : V) (hx : x ∈ D) (hy : y ∈ D) :
    Bool.xor (c x) (c (p x)) =
      Bool.xor (c y) (c (p y)) := by
  by_cases hxy : x = y
  · subst y
    rfl
  have hpPair := hp x y hx hy
  have hColors : (c x = c y) ↔ (c (p x) = c (p y)) := by
    change (x ≠ y ∧ c x = c y) ↔
      (p x ≠ p y ∧ c (p x) = c (p y)) at hpPair
    simpa [hxy, p.injective.ne hxy] using hpPair
  cases hcx : c x <;> cases hcy : c y <;>
    cases hcpx : c (p x) <;> cases hcpy : c (p y) <;>
    simp_all [Bool.xor]

/-- The selected bottom layer induces exactly the original
two-clique graph for either value of the mate bit. -/
theorem twoClique_matched_bottom_induced
    {V : Type*} (c : V → Bool) (mate : Bool) :
    IsInducedGraphEmbedding (twoCliqueGraph c)
      (twoCliqueMatchedGraph c mate) (bottomEmbedding V) := by
  intro x y
  by_cases hxy : x = y
  · subst y
    simp [twoCliqueGraph, twoCliqueMatchedGraph,
      bottomEmbedding, Bool.xor]
  · simp [twoCliqueGraph, twoCliqueMatchedGraph,
      twoCliqueMatchedRel, bottomEmbedding, hxy, Bool.xor]

/-- A *nonhomogeneous* two-clique base nevertheless has an EPPA
double for either mate bit. No homogeneity of the base is assumed. -/
theorem twoClique_matched_isEPPA
    {V : Type*} (c : V → Bool) (mate : Bool) :
    IsEPPAEmbedding (twoCliqueGraph c)
      (twoCliqueMatchedGraph c mate) (bottomEmbedding V) := by
  classical
  refine ⟨twoClique_matched_bottom_induced c mate, ?_⟩
  intro D p hp
  by_cases hD : D.Nonempty
  · obtain ⟨x0, hx0⟩ := hD
    let delta : Bool := Bool.xor (c x0) (c (p x0))
    refine ⟨twoCliqueMatchedSymmetry c p delta,
      twoCliqueMatchedSymmetry_graphAut c mate p delta, ?_⟩
    intro x hx
    have hDelta : Bool.xor (c x) (c (p x)) = delta :=
      twoClique_partial_color_discrepancy c D p hp x x0 hx hx0
    change
      (Bool.xor (Bool.xor (Bool.xor false (c x))
        (c (p x))) delta, p x) = (false, p x)
    apply Prod.ext
    · cases hcx : c x <;> cases hcpx : c (p x) <;>
        cases hd : delta <;>
        simp_all [Bool.xor]
    · rfl
  · refine ⟨twoCliqueMatchedSymmetry c p false,
      twoCliqueMatchedSymmetry_graphAut c mate p false, ?_⟩
    intro x hx
    exact (hD ⟨x,hx⟩).elim

/-- Every canonical two-clique double with uniformly optional mate
matching is vertex transitive, regardless of the base clique sizes. -/
theorem twoClique_matched_vertexTransitive
    {V : Type*} (c : V → Bool) (mate : Bool) :
    IsVertexTransitive (twoCliqueMatchedGraph c mate) := by
  classical
  intro u v
  let p : Equiv.Perm V := Equiv.swap u.2 v.2
  have hp : p u.2 = v.2 := by simp [p]
  let delta : Bool :=
    Bool.xor (Bool.xor u.1 (c u.2)) (Bool.xor v.1 (c v.2))
  refine ⟨twoCliqueMatchedSymmetry c p delta,
    twoCliqueMatchedSymmetry_graphAut c mate p delta, ?_⟩
  apply Prod.ext
  · change
      Bool.xor
        (Bool.xor (Bool.xor u.1 (c u.2)) (c (p u.2)))
          delta = v.1
    rw [hp]
    cases hu : u.1 <;> cases hv : v.1 <;>
      cases hcu : c u.2 <;> cases hcv : c v.2 <;>
      simp [delta, hu, hv, hcu, hcv, Bool.xor]
  · exact hp

end EPPAIII.BlockSystems
