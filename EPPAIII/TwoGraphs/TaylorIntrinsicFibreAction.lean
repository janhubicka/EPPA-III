import EPPAIII.TwoGraphs.IntrinsicTaylorMates
import EPPAIII.DoubleCover.TwoPointAction

/-!
# Deriving the invariant Taylor fibre partition from intrinsic mates

The mate of (b,x) is the unique vertex at shortest graph-walk
distance three, provided every two distinct base vertices belong
to an even-parity triple. Because this relation is preserved by
graph automorphisms, every automorphism of the host induces a
permutation of the base indices.

No finite-cardinality argument or auxiliary coherent EPPA choice
is needed. The inverse induced permutation is defined using the
inverse host automorphism.
-/

namespace EPPAIII.TwoGraphs

/-- Fibre preservation is forced by adjacency alone in a canonical
Taylor double satisfying the even-triple pair coverage hypothesis. -/
theorem taylor_invariant_pairs_of_even_coverage
    {V : Type*} [Nontrivial V]
    (G : SimpleGraph V)
    (hCoverage : ∀ x y : V, x ≠ y →
      ∃ z : V, x ≠ z ∧ y ≠ z ∧ EvenTriple G x y z) :
    EPPAIII.DoubleCover.HasInvariantPairs (taylorPairGraph G) := by
  intro q hq
  have hInv : EPPAIII.IsGraphAutomorphism
      (taylorPairGraph G) q.symm := by
    intro u v
    simpa using (hq (q.symm u) (q.symm v)).symm
  let sf : V → V := fun x => (q (false,x)).2
  let tf : V → V := fun x => (q.symm (false,x)).2
  have hS (b : Bool) (x : V) :
      (q (b,x)).2 = sf x := by
    cases b with
    | false =>
        change (q (false,x)).2 = (q (false,x)).2
        rfl
    | true =>
        change (q (true,x)).2 = (q (false,x)).2
        have hh := taylor_automorphism_preserves_mate_second
          G hCoverage q hq false x
        simpa using hh.symm
  have hT (b : Bool) (x : V) :
      (q.symm (b,x)).2 = tf x := by
    cases b with
    | false =>
        change (q.symm (false,x)).2 = (q.symm (false,x)).2
        rfl
    | true =>
        change (q.symm (true,x)).2 = (q.symm (false,x)).2
        have hh := taylor_automorphism_preserves_mate_second
          G hCoverage q.symm hInv false x
        simpa using hh.symm
  have hLeft (x : V) : tf (sf x) = x := by
    let p : Bool × V := q (false,x)
    have hp : q.symm p = (false,x) := by simp [p]
    calc
      tf (sf x) = tf p.2 := rfl
      _ = (q.symm (p.1,p.2)).2 := (hT p.1 p.2).symm
      _ = x := by simpa [p] using congrArg Prod.snd hp
  have hRight (x : V) : sf (tf x) = x := by
    let p : Bool × V := q.symm (false,x)
    have hp : q p = (false,x) := by simp [p]
    calc
      sf (tf x) = sf p.2 := rfl
      _ = (q (p.1,p.2)).2 := (hS p.1 p.2).symm
      _ = x := by simpa [p] using congrArg Prod.snd hp
  let σ : Equiv.Perm V :=
    { toFun := sf
      invFun := tf
      left_inv := hLeft
      right_inv := hRight }
  refine ⟨σ,?_⟩
  intro b x
  exact hS b x

end EPPAIII.TwoGraphs
