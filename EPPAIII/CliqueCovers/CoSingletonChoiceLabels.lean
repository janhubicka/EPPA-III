import EPPAIII.CliqueCovers.SingletonChoiceLabels

/-!
# Canonical labels for one-position co-singleton profile choices

When t>0, choosing t-1 vertices of a t-element clique
is equivalent to specifying the one omitted point.
Thus a one-coordinate co-singleton profile choice is canonically
indexed by its clique number and its omitted point, giving the same
natural Fin s × Fin t labelling as the singleton case.

The precise nonemptiness hypothesis excludes t=0, when the
choice space has size s but Fin s × Fin 0 is empty.
Equivariance under actual EPPA lifts is a separate next step.
-/

namespace EPPAIII.CliqueCovers

/-- The admissible choice with one selected index i and all
points of its clique except a. -/
noncomputable def coSingletonChoiceOfPair {s t : ℕ}
    (x : Fin s × Fin t) :
    AdmissibleProfileChoice s t 1 (t - 1) := by
  classical
  refine ⟨⟨({x.1} : Finset (Fin s)),
      fun _ _ => (({x.2} : Finset (Fin t))ᶜ)⟩, ?_⟩
  apply (mem_profileChoiceSpace_iff s t 1 (t - 1)
    ({x.1} : Finset (Fin s))
    (fun _ _ => (({x.2} : Finset (Fin t))ᶜ))).mpr
  constructor
  · simp
  · intro i hi
    simp [Finset.card_compl]

theorem coSingletonChoiceOfPair_positions {s t : ℕ}
    (x : Fin s × Fin t) :
    (coSingletonChoiceOfPair x).val.1 = {x.1} := by
  rfl

theorem coSingletonChoiceOfPair_slice {s t : ℕ}
    (x : Fin s × Fin t) :
    admissibleChoiceSlice (coSingletonChoiceOfPair x) x.1 =
      (({x.2} : Finset (Fin t))ᶜ) := by
  classical
  simp [admissibleChoiceSlice, coSingletonChoiceOfPair]

theorem coSingletonChoiceOfPair_injective (s t : ℕ) :
    Function.Injective
      (coSingletonChoiceOfPair (s := s) (t := t)) := by
  classical
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  have hPositions : ({i} : Finset (Fin s)) = {j} := by
    simpa [coSingletonChoiceOfPair_positions] using
      (congrArg
        (fun choice : AdmissibleProfileChoice s t 1 (t-1) =>
          choice.val.1) h)
  have hij : i = j := by
    have hi : i ∈ ({j} : Finset (Fin s)) := by
      rw [← hPositions]
      simp
    simpa using hi
  subst j
  have hSlices :
      (({a} : Finset (Fin t))ᶜ) =
        (({b} : Finset (Fin t))ᶜ) := by
    have hs := congrArg
      (fun choice : AdmissibleProfileChoice s t 1 (t-1) =>
        admissibleChoiceSlice choice i) h
    simpa [admissibleChoiceSlice, coSingletonChoiceOfPair] using hs
  have hab : a = b := by
    have ha : a ∉ (({b} : Finset (Fin t))ᶜ) := by
      rw [← hSlices]
      simp
    simpa using ha
  subst b
  rfl

theorem coSingletonChoiceOfPair_surjective
    (s t : ℕ) (ht : 0 < t) :
    Function.Surjective
      (coSingletonChoiceOfPair (s := s) (t := t)) := by
  classical
  intro choice
  rcases choice with ⟨⟨R,A⟩,hc⟩
  obtain ⟨hR,hA⟩ :=
    (mem_profileChoiceSpace_iff s t 1 (t - 1) R A).mp hc
  obtain ⟨i,hRi⟩ := Finset.card_eq_one.mp hR
  subst R
  have hi : i ∈ ({i} : Finset (Fin s)) := by simp
  have hAcard : (A i hi).card = t - 1 := hA i hi
  have hComplCard :
      ((A i hi)ᶜ : Finset (Fin t)).card = 1 := by
    have hCard :
        ((A i hi)ᶜ : Finset (Fin t)).card =
          t - (A i hi).card := by
      simp [Finset.card_compl]
    rw [hCard, hAcard]
    omega
  obtain ⟨a,hComplement⟩ := Finset.card_eq_one.mp hComplCard
  have hAi :
      A i hi = (({a} : Finset (Fin t))ᶜ) := by
    have hComp :=
      congrArg (fun Z : Finset (Fin t) => Zᶜ) hComplement
    simpa using hComp
  refine ⟨(i,a), ?_⟩
  apply Subtype.ext
  change
    (⟨({i} : Finset (Fin s)),
      fun (_j : Fin s) (_hj : _j ∈ ({i} : Finset (Fin s))) =>
        (({a} : Finset (Fin t))ᶜ)⟩ :
      Σ R : Finset (Fin s), ∀ j : Fin s, j ∈ R → Finset (Fin t)) =
    ⟨{i},A⟩
  congr 1
  funext j hj
  have hji : j = i := by simpa using hj
  subst j
  simpa using hAi.symm

/-- Explicit canonical co-singleton labels; the second coordinate
records the missing point, not any chosen neighbour. -/
noncomputable def coSingletonChoiceEquiv (s t : ℕ) (ht : 0 < t) :
    (Fin s × Fin t) ≃ AdmissibleProfileChoice s t 1 (t - 1) :=
  Equiv.ofBijective coSingletonChoiceOfPair
    ⟨coSingletonChoiceOfPair_injective s t,
     coSingletonChoiceOfPair_surjective s t ht⟩

@[simp] theorem coSingletonChoiceEquiv_apply (s t : ℕ) (ht : 0 < t)
    (x : Fin s × Fin t) :
    coSingletonChoiceEquiv s t ht x =
      coSingletonChoiceOfPair x := by
  rfl

end EPPAIII.CliqueCovers
