module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.EquivFin

/-!
# Permuting two finite families with equal intersection sizes

This is the finite set lemma used in the triangular graph witness theorem.
-/

namespace EPPAIII.Primitive

open Finset

variable {I V : Type*} [Fintype V] [DecidableEq V]

private noncomputable def restrictedIntersection (A : I → Finset V)
    (positive negative : Finset I) : Finset V := by
  classical
  exact univ.filter fun v => (∀ i ∈ positive, v ∈ A i) ∧ (∀ i ∈ negative, v ∉ A i)

private theorem restrictedIntersection_card_eq (A B : I → Finset V)
    (h : ∀ J : Finset I, (univ.filter fun v => ∀ i ∈ J, v ∈ A i).card =
      (univ.filter fun v => ∀ i ∈ J, v ∈ B i).card)
    (positive negative : Finset I) :
    (restrictedIntersection A positive negative).card =
      (restrictedIntersection B positive negative).card := by
  classical
  induction negative using Finset.induction_on generalizing positive with
  | empty =>
    simpa [restrictedIntersection] using h positive
  | insert i negative _ ih =>
    have split (C : I → Finset V) :
        (restrictedIntersection C (insert i positive) negative).card +
          (restrictedIntersection C positive (insert i negative)).card =
            (restrictedIntersection C positive negative).card := by
      have positiveFilter : (restrictedIntersection C positive negative).filter (· ∈ C i) =
          restrictedIntersection C (insert i positive) negative := by
        ext v
        simp [restrictedIntersection, and_left_comm, and_comm]
      have negativeFilter : (restrictedIntersection C positive negative).filter (· ∉ C i) =
          restrictedIntersection C positive (insert i negative) := by
        ext v
        simp [restrictedIntersection, and_assoc, and_comm]
      simpa only [positiveFilter, negativeFilter] using
        (restrictedIntersection C positive negative).card_filter_add_card_filter_not (· ∈ C i)
    exact Nat.add_left_cancel <| calc
      _ = (restrictedIntersection A positive negative).card := split A
      _ = (restrictedIntersection B positive negative).card := ih positive
      _ = _ := by rw [ih (insert i positive), split B]

variable [Fintype I]

private def membershipProfile (A : I → Finset V) (v : V) : Finset I :=
  univ.filter fun i => v ∈ A i

private theorem filter_membershipProfile_eq (A : I → Finset V) [DecidableEq I] (J : Finset I) :
    univ.filter (fun v => membershipProfile A v = J) =
      restrictedIntersection A J (univ \ J) := by
  ext v
  simp only [mem_filter, mem_univ, true_and, restrictedIntersection]
  constructor
  · intro h
    constructor
    · intro i hi
      have : i ∈ membershipProfile A v := by rwa [h]
      simpa [membershipProfile] using this
    · intro i hi hv
      have : i ∈ membershipProfile A v := by simp [membershipProfile, hv]
      exact (mem_sdiff.mp hi).2 (h ▸ this)
  · rintro ⟨positive, negative⟩
    ext i
    simp only [membershipProfile, mem_filter, mem_univ, true_and]
    refine ⟨?_, positive i⟩
    intro hv
    by_contra hi
    exact negative i (by simp [hi]) hv

/-- Equal sizes of all indexed intersections give a single permutation
mapping each of the sets in the first family to the corresponding set in the second. -/
public theorem exists_perm_of_intersection_card_eq (A B : I → Finset V)
    (h : ∀ J : Finset I, (univ.filter fun v => ∀ i ∈ J, v ∈ A i).card =
      (univ.filter fun v => ∀ i ∈ J, v ∈ B i).card) :
    ∃ e : Equiv.Perm V, ∀ i, (A i).map e.toEmbedding = B i := by
  classical
  have exactCounts (J : Finset I) :
      (univ.filter fun v => membershipProfile A v = J).card =
        (univ.filter fun v => membershipProfile B v = J).card := by
    rw [filter_membershipProfile_eq, filter_membershipProfile_eq]
    exact restrictedIntersection_card_eq A B h J (univ \ J)
  let fiber (C : I → Finset V) (J : Finset I) :
      {v // membershipProfile C v = J} ≃ ↑(univ.filter fun v => membershipProfile C v = J) :=
    Equiv.subtypeEquivRight fun _ => by simp
  let fiberEquiv (J : Finset I) : {v // membershipProfile A v = J} ≃
      {v // membershipProfile B v = J} :=
    (fiber A J).trans ((Finset.equivOfCardEq (exactCounts J)).trans (fiber B J).symm)
  let e : Equiv.Perm V := Equiv.ofFiberEquiv fiberEquiv
  refine ⟨e, fun i => Finset.ext fun v => ?_⟩
  have profileEq := Equiv.ofFiberEquiv_map fiberEquiv (e.symm v)
  change membershipProfile B (e (e.symm v)) = membershipProfile A (e.symm v) at profileEq
  rw [e.apply_symm_apply] at profileEq
  have memEq := congrArg (fun J : Finset I => i ∈ J) profileEq.symm
  simpa [membershipProfile] using Iff.of_eq memEq

end EPPAIII.Primitive
