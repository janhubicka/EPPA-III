import EPPAIII.CliqueCovers.OutsideChoiceEquiv
import EPPAIII.CliqueCovers.OutsideLiftTransport

/-!
# Canonical four-corner labels of the exceptional double-partial orbit

When s=t=2 and both base-clique coordinates have exactly one
neighbour, every admissible profile choice consists of a singleton
from each of the two distinguished cliques.

The four possibilities are canonically indexed by Bool × Bool:
each Boolean specifies which vertex in its base K₂ is selected.
No arbitrary enumeration of outside vertices or coherent choice of
EPPA extensions is used.

This is the exact finite coordinate interface for transporting the
two-partial EPPA witness to the square-action graph in Section 3.
-/

namespace EPPAIII.CliqueCovers

/-- The formal two-partial profile with one chosen vertex in each
base K₂, indexed by its two Boolean coordinates. -/
noncomputable def squareChoiceOfPair
    (x : Bool × Bool) : AdmissibleProfileChoice 2 2 2 1 := by
  classical
  let a : Fin 2 := finTwoEquiv.symm x.1
  let b : Fin 2 := finTwoEquiv.symm x.2
  refine ⟨⟨Finset.univ,
    fun i _ => {if i = (0 : Fin 2) then a else b}⟩, ?_⟩
  apply (mem_profileChoiceSpace_iff 2 2 2 1
    (Finset.univ : Finset (Fin 2))
    (fun i _ => {if i = (0 : Fin 2) then a else b})).mpr
  constructor
  · simp
  · intro i hi
    simp

/-- The first coordinate determines the chosen singleton in clique 0. -/
theorem squareChoiceOfPair_first (x : Bool × Bool) :
    admissibleChoiceSlice (squareChoiceOfPair x) (0 : Fin 2) =
      ({finTwoEquiv.symm x.1} : Finset (Fin 2)) := by
  classical
  simp [admissibleChoiceSlice, squareChoiceOfPair]

/-- The second coordinate determines the chosen singleton in clique 1. -/
theorem squareChoiceOfPair_second (x : Bool × Bool) :
    admissibleChoiceSlice (squareChoiceOfPair x) (1 : Fin 2) =
      ({finTwoEquiv.symm x.2} : Finset (Fin 2)) := by
  classical
  simp [admissibleChoiceSlice, squareChoiceOfPair]

/-- Distinct corners yield distinct admissible two-partial choices. -/
theorem squareChoiceOfPair_injective :
    Function.Injective squareChoiceOfPair := by
  classical
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hFirst := congrArg
    (fun z : AdmissibleProfileChoice 2 2 2 1 =>
      admissibleChoiceSlice z (0 : Fin 2)) h
  have hSecond := congrArg
    (fun z : AdmissibleProfileChoice 2 2 2 1 =>
      admissibleChoiceSlice z (1 : Fin 2)) h
  have hFirst' :
      ({finTwoEquiv.symm a} : Finset (Fin 2)) =
        {finTwoEquiv.symm c} := by
    simpa [squareChoiceOfPair_first] using hFirst
  have hSecond' :
      ({finTwoEquiv.symm b} : Finset (Fin 2)) =
        {finTwoEquiv.symm d} := by
    simpa [squareChoiceOfPair_second] using hSecond
  have hac : a = c := by
    apply finTwoEquiv.symm.injective
    have hMem : finTwoEquiv.symm a ∈
        ({finTwoEquiv.symm c} : Finset (Fin 2)) := by
      rw [← hFirst']
      simp
    simpa using hMem
  have hbd : b = d := by
    apply finTwoEquiv.symm.injective
    have hMem : finTwoEquiv.symm b ∈
        ({finTwoEquiv.symm d} : Finset (Fin 2)) := by
      rw [← hSecond']
      simp
    simpa using hMem
  exact Prod.ext hac hbd

/-- There are exactly four admissible 2-by-2 double-partial choices. -/
theorem squareChoiceSpace_card :
    Fintype.card (AdmissibleProfileChoice 2 2 2 1) = 4 := by
  classical
  change Fintype.card ↥(profileChoiceSpace 2 2 2 1) = 4
  rw [Fintype.card_coe, profileChoiceSpace_card]
  norm_num

/-- Every formal two-partial choice comes from exactly one corner. -/
theorem squareChoiceOfPair_bijective :
    Function.Bijective squareChoiceOfPair := by
  apply (Fintype.bijective_iff_injective_and_card
    squareChoiceOfPair).2
  constructor
  · exact squareChoiceOfPair_injective
  · simpa [squareChoiceSpace_card]

/-- Canonical four-corner equivalence, independent of any EPPA
extension choices. -/
noncomputable def squareChoiceEquiv :
    (Bool × Bool) ≃ AdmissibleProfileChoice 2 2 2 1 :=
  Equiv.ofBijective squareChoiceOfPair
    squareChoiceOfPair_bijective

@[simp] theorem squareChoiceEquiv_apply (x : Bool × Bool) :
    squareChoiceEquiv x = squareChoiceOfPair x := by
  rfl

end EPPAIII.CliqueCovers
