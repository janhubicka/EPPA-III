import EPPAIII.TwoGraphs.PartialSwitchFull

/-!
# Partial two-graph switching for arbitrary partial injections

The core Lean interface represents a partial bijection by
restricting a total permutation of the finite vertex set.
This file explicitly certifies that no generality is lost:
every injective function on a finite prescribed domain extends
to a total permutation, and the already verified switching
theorem transfers back to the original partial injection.

This is the exact source-facing form of Lemma 5.1 in which the
partial automorphism itself need not be defined outside its domain.
-/

namespace EPPAIII.TwoGraphs

/-- Every injective partial two-graph map of a finite graph is
a partial graph isomorphism of some switched representative.

The function f is arbitrary outside D; only injectivity and
preservation of odd triples *on D* are assumed. -/
theorem partial_two_graph_injection_has_switch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (f : V → V)
    (hInjective : ∀ x ∈ D, ∀ y ∈ D, f x = f y → x = y)
    (hTriples : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D,
      OddBaseTriple G x y z ↔
        OddBaseTriple G (f x) (f y) (f z)) :
    ∃ t : V → Bool,
      ∀ x ∈ D, ∀ y ∈ D,
        (taylorTransversalGraph G t).Adj x y ↔
          (taylorTransversalGraph G t).Adj (f x) (f y) := by
  classical
  let U := {x : V // x ∈ D}
  have hEmbedding : Function.Injective (fun a : U => f a.1) := by
    intro a b h
    exact Subtype.ext
      (hInjective a.1 a.2 b.1 b.2 h)
  obtain ⟨p,hExt⟩ :=
    Equiv.Perm.exists_extending_pair
      (fun a : U => (a.1 : V))
      (fun a : U => f a.1)
      Subtype.val_injective hEmbedding
  have hPartial : IsPartialTwoGraphAutomorphism G D p := by
    intro x hx y hy z hz
    have h := hTriples x hx y hy z hz
    simpa only [hExt ⟨x,hx⟩, hExt ⟨y,hy⟩, hExt ⟨z,hz⟩] using h
  obtain ⟨t,hSwitch⟩ :=
    partial_two_graph_has_switching_representative G D p hPartial
  refine ⟨t, ?_⟩
  intro x hx y hy
  have h := hSwitch x y hx hy
  simpa only [hExt ⟨x,hx⟩, hExt ⟨y,hy⟩] using h

end EPPAIII.TwoGraphs
