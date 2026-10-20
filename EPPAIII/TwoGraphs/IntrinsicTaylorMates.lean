import EPPAIII.TwoGraphs.TaylorFibresDistance
import EPPAIII.EPPA.Definitions

/-!
# Intrinsic fibre mates as vertices at graph distance three

Use an elementary first-order formulation of distance three:
there is a walk of length exactly three but none of length
one or two. Under even-triple pair coverage the canonical
Taylor mates are exactly the pairs with this property.

This is a theorem solely about the Taylor graph's adjacency,
independent of automorphism, EPPA and any quotient construction.
-/

namespace EPPAIII.TwoGraphs

/-- A three-edge walk with no shorter walk. For simple graphs
the absence of length-two walks also excludes equal endpoints
whenever a three-edge walk exists. -/
def ThreeStepShortest {W : Type*} (H : SimpleGraph W)
    (u v : W) : Prop :=
  (∃ p q : W, H.Adj u p ∧ H.Adj p q ∧ H.Adj q v) ∧
    ¬ H.Adj u v ∧
    ¬ ∃ p : W, H.Adj u p ∧ H.Adj p v

/-- Every graph automorphism preserves the shortest-three relation,
because its definition uses only adjacency and nonadjacency. -/
theorem threeStepShortest_forward {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) (u v : W) :
    ThreeStepShortest H u v →
      ThreeStepShortest H (q u) (q v) := by
  rintro ⟨⟨p,r,hUp,hPr,hRv⟩,hNoEdge,hNoTwo⟩
  refine ⟨⟨q p,q r,(hq u p).mp hUp,(hq p r).mp hPr,
      (hq r v).mp hRv⟩, ?_, ?_⟩
  · intro hEdge
    exact hNoEdge ((hq u v).mpr hEdge)
  · rintro ⟨s,hUs,hSv⟩
    let p' : W := q.symm s
    have hFirst : H.Adj u p' := by
      apply (hq u p').mpr
      simpa [p'] using hUs
    have hSecond : H.Adj p' v := by
      apply (hq p' v).mpr
      simpa [p'] using hSv
    exact hNoTwo ⟨p',hFirst,hSecond⟩

theorem threeStepShortest_automorphism_iff {W : Type*}
    (H : SimpleGraph W) (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) (u v : W) :
    ThreeStepShortest H u v ↔
      ThreeStepShortest H (q u) (q v) := by
  have hInv : EPPAIII.IsGraphAutomorphism H q.symm := by
    intro a b
    simpa only [q.apply_symm_apply] using
      (hq (q.symm a) (q.symm b)).symm
  constructor
  · exact threeStepShortest_forward H q hq u v
  · intro hh
    have hBack :=
      threeStepShortest_forward H q.symm hInv
        (q u) (q v) hh
    simpa using hBack

/-- With every base pair in an even triple, shortest-three
partners are exactly the two canonical lifts of the same point. -/
theorem taylor_threeStepShortest_iff_mate {V : Type*}
    [Nontrivial V]
    (G : SimpleGraph V)
    (hCoverage : ∀ x y : V, x ≠ y →
      ∃ z : V, x ≠ z ∧ y ≠ z ∧ EvenTriple G x y z)
    (b c : Bool) (x y : V) :
    ThreeStepShortest (taylorPairGraph G) (b,x) (c,y) ↔
      (x = y ∧ c = !b) := by
  constructor
  · intro hShortest
    by_cases hxy : x = y
    · subst y
      have hbc : b ≠ c := by
        intro h
        subst c
        obtain ⟨p,q,hUp,_,_⟩ := hShortest.1
        apply hShortest.2.2
        exact ⟨p,hUp,
          ((taylorPairGraph G).adj_comm _ _).mp hUp⟩
      have hc : c = !b := by
        cases b <;> cases c <;> simp_all
      exact ⟨rfl,hc⟩
    · rcases taylor_other_fibres_at_most_two
        G hCoverage b c x y hxy with hEdge | ⟨p,hUp,hPv⟩
      · exact False.elim (hShortest.2.1 hEdge)
      · exact False.elim (hShortest.2.2 ⟨p,hUp,hPv⟩)
  · rintro ⟨rfl,hc⟩
    subst c
    obtain ⟨hThree,hNoEdge,hNoCommon⟩ :=
      taylor_mates_three_and_not_shorter G hCoverage b x
    refine ⟨hThree,hNoEdge,?_⟩
    rintro ⟨p,hUp,hPv⟩
    exact hNoCommon ⟨p,hUp,
      ((taylorPairGraph G).adj_comm _ _).mpr hPv⟩

/-- Intrinsic shortest-three partners must have the same second
coordinate after every automorphism of the Taylor graph. -/
theorem taylor_automorphism_preserves_mate_second {V : Type*}
    [Nontrivial V]
    (G : SimpleGraph V)
    (hCoverage : ∀ x y : V, x ≠ y →
      ∃ z : V, x ≠ z ∧ y ≠ z ∧ EvenTriple G x y z)
    (q : Equiv.Perm (Bool × V))
    (hq : EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q)
    (b : Bool) (x : V) :
    (q (b,x)).2 = (q (!b,x)).2 := by
  have hBefore :
      ThreeStepShortest (taylorPairGraph G)
        (b,x) (!b,x) :=
    (taylor_threeStepShortest_iff_mate G hCoverage
      b (!b) x x).mpr ⟨rfl,rfl⟩
  have hAfter :
      ThreeStepShortest (taylorPairGraph G)
        (q (b,x)) (q (!b,x)) :=
    (threeStepShortest_automorphism_iff
      (taylorPairGraph G) q hq _ _).mp hBefore
  have hShape :=
    (taylor_threeStepShortest_iff_mate G hCoverage
      (q (b,x)).1 (q (!b,x)).1
      (q (b,x)).2 (q (!b,x)).2).mp
      (by simpa only [Prod.mk.eta] using hAfter)
  exact hShape.1

end EPPAIII.TwoGraphs
