import EPPAIII.CliqueCovers.OutsideChoiceEquiv

/-!
# Canonical coordinates for one-position singleton profile choices

The saturated one-partial case has exactly one selected size-k
coordinate, and k is either 1 or t-1.  In the singleton case every
admissible choice consists of one clique index i and one point a in
that clique.  This file constructs the explicit *canonical*
equivalence between Fin s × Fin t and the existing dependent
choice-space type, rather than choosing an arbitrary same-cardinality
equivalence.

The complementary (co-singleton) case and equivariance of this
equivalence under EPPA lifts are subsequent proof obligations.
-/

namespace EPPAIII.CliqueCovers

/-- Totalize the dependent slice of a combinatorial choice by
returning the empty set off its selected indices. -/
noncomputable def admissibleChoiceSlice {s t r k : ℕ}
    (choice : AdmissibleProfileChoice s t r k)
    (i : Fin s) : Finset (Fin t) := by
  classical
  exact if hi : i ∈ choice.val.1 then choice.val.2 i hi else ∅

/-- The admissible choice selecting the singleton coordinate i and
the singleton point a. -/
noncomputable def singletonChoiceOfPair {s t : ℕ}
    (x : Fin s × Fin t) : AdmissibleProfileChoice s t 1 1 := by
  classical
  refine ⟨⟨({x.1} : Finset (Fin s)), fun _ _ => ({x.2} : Finset (Fin t))⟩, ?_⟩
  apply (mem_profileChoiceSpace_iff s t 1 1
    ({x.1} : Finset (Fin s))
    (fun _ _ => ({x.2} : Finset (Fin t)))).mpr
  constructor
  · simp
  · intro i hi
    simp

/-- The chosen position is precisely the first coordinate. -/
theorem singletonChoiceOfPair_positions {s t : ℕ}
    (x : Fin s × Fin t) :
    (singletonChoiceOfPair x).val.1 = {x.1} := by
  rfl

/-- The chosen slice at its position is precisely the singleton
of the second coordinate. -/
theorem singletonChoiceOfPair_slice {s t : ℕ}
    (x : Fin s × Fin t) :
    admissibleChoiceSlice (singletonChoiceOfPair x) x.1 = {x.2} := by
  classical
  simp [admissibleChoiceSlice, singletonChoiceOfPair]

/-- Different pairs give different admissible singleton choices. -/
theorem singletonChoiceOfPair_injective (s t : ℕ) :
    Function.Injective
      (singletonChoiceOfPair (s := s) (t := t)) := by
  classical
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hPositions : ({i} : Finset (Fin s)) = {j} := by
    simpa [singletonChoiceOfPair_positions] using
      (congrArg
        (fun choice : AdmissibleProfileChoice s t 1 1 => choice.val.1) h)
  have hij : i = j := by
    have hi : i ∈ ({j} : Finset (Fin s)) := by
      rw [← hPositions]
      simp
    simpa using hi
  subst j
  have hSlices :
      ({a} : Finset (Fin t)) = {b} := by
    have hs := congrArg
      (fun choice : AdmissibleProfileChoice s t 1 1 =>
        admissibleChoiceSlice choice i) h
    simpa only [singletonChoiceOfPair_slice] using hs
  have hab : a = b := by
    have ha : a ∈ ({b} : Finset (Fin t)) := by
      rw [← hSlices]
      simp
    simpa using ha
  subst b
  rfl

/-- Every admissible choice with one selected singleton coordinate
comes from a pair (i,a). -/
theorem singletonChoiceOfPair_surjective (s t : ℕ) :
    Function.Surjective
      (singletonChoiceOfPair (s := s) (t := t)) := by
  classical
  intro choice
  rcases choice with ⟨⟨R,A⟩,hc⟩
  obtain ⟨hR,hA⟩ :=
    (mem_profileChoiceSpace_iff s t 1 1 R A).mp hc
  obtain ⟨i,hRi⟩ := Finset.card_eq_one.mp hR
  subst R
  have hi : i ∈ ({i} : Finset (Fin s)) := by simp
  obtain ⟨a,hAi⟩ := Finset.card_eq_one.mp (hA i hi)
  refine ⟨(i,a), ?_⟩
  apply Subtype.ext
  change
    (⟨({i} : Finset (Fin s)),
      fun (_j : Fin s) (_hj : _j ∈ ({i} : Finset (Fin s))) =>
        ({a} : Finset (Fin t))⟩ :
      Σ R : Finset (Fin s), ∀ j : Fin s, j ∈ R → Finset (Fin t)) =
    ⟨{i},A⟩
  apply Sigma.ext rfl
  apply heq_of_eq
  funext j hj
  have hji : j = i := by simpa using hj
  subst j
  simpa using hAi.symm

/-- The canonical, explicitly indexed equivalence of singleton
profile choices with Fin s × Fin t. -/
noncomputable def singletonChoiceEquiv (s t : ℕ) :
    (Fin s × Fin t) ≃ AdmissibleProfileChoice s t 1 1 :=
  Equiv.ofBijective singletonChoiceOfPair
    ⟨singletonChoiceOfPair_injective s t,
     singletonChoiceOfPair_surjective s t⟩

@[simp] theorem singletonChoiceEquiv_apply (s t : ℕ)
    (x : Fin s × Fin t) :
    singletonChoiceEquiv s t x = singletonChoiceOfPair x := by
  rfl

end EPPAIII.CliqueCovers
