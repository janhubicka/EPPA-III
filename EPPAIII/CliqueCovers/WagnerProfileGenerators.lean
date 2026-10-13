import EPPAIII.CliqueCovers.WagnerSquareChoiceLabels
import EPPAIII.CliqueCovers.WagnerSquareAction
import EPPAIII.CliqueCovers.WreathProfileEquivariance

/-!
# The three base wreath generators act on Wagner square profiles

In the exceptional s=t=2 two-partial case, an outside profile has
one selected point in each of the two base K₂'s. Write it explicitly
as the two-element finite set squareProfile(x), where x∈Bool×Bool.

The two independent within-clique swaps and the swap of the two
clique indices act on these profiles by the three generators of
the natural square action. These are exact finite-set equations,
not an appeal to coherence of arbitrary EPPA lifts.

The subsequent host-level application uses the verified EPPA
profile-transport lemma to move the actual outside vertices.
-/

namespace EPPAIII.CliqueCovers

/-- The two singleton base-neighbourhood positions of corner x. -/
def squareProfile (x : Bool × Bool) : Finset (Fin 2 × Fin 2) :=
  {((0 : Fin 2), finTwoEquiv.symm x.1),
   ((1 : Fin 2), finTwoEquiv.symm x.2)}

/-- The first designated clique has the first selected point. -/
theorem squareProfile_first (x : Bool × Bool) :
    profileSlice (squareProfile x) (0 : Fin 2) =
      {finTwoEquiv.symm x.1} := by
  classical
  ext z
  simp [squareProfile, profileSlice]

/-- The second designated clique has the second selected point. -/
theorem squareProfile_second (x : Bool × Bool) :
    profileSlice (squareProfile x) (1 : Fin 2) =
      {finTwoEquiv.symm x.2} := by
  classical
  ext z
  simp [squareProfile, profileSlice]

/-- A full two-partial profile is determined by its two singleton slices. -/
theorem squareProfile_eq_of_slices
    (P : Finset (Fin 2 × Fin 2)) (x : Bool × Bool)
    (h0 : profileSlice P (0 : Fin 2) = {finTwoEquiv.symm x.1})
    (h1 : profileSlice P (1 : Fin 2) = {finTwoEquiv.symm x.2}) :
    P = squareProfile x := by
  apply profile_eq_of_slices
  intro i
  fin_cases i
  · simpa [squareProfile_first] using h0
  · simpa [squareProfile_second] using h1

/-- Swap the vertices in the first base clique only. -/
def squareBaseFlipFirst : Equiv.Perm (Fin 2 × Fin 2) :=
  innerPermutation (fun i =>
    if i = (0 : Fin 2) then Equiv.swap (0 : Fin 2) 1 else Equiv.refl _)

/-- Swap the vertices in the second base clique only. -/
def squareBaseFlipSecond : Equiv.Perm (Fin 2 × Fin 2) :=
  innerPermutation (fun i =>
    if i = (1 : Fin 2) then Equiv.swap (0 : Fin 2) 1 else Equiv.refl _)

/-- Swap the two base cliques without changing internal coordinates. -/
def squareBaseSwapCoordinates : Equiv.Perm (Fin 2 × Fin 2) :=
  outerPermutation (Equiv.swap (0 : Fin 2) 1)

theorem squareBaseFlipFirst_graphAut :
    IsGraphAutomorphism (cliqueUnion 2 2) squareBaseFlipFirst :=
  innerPermutation_aut _

theorem squareBaseFlipSecond_graphAut :
    IsGraphAutomorphism (cliqueUnion 2 2) squareBaseFlipSecond :=
  innerPermutation_aut _

theorem squareBaseSwapCoordinates_graphAut :
    IsGraphAutomorphism (cliqueUnion 2 2) squareBaseSwapCoordinates :=
  outerPermutation_aut _

/-- The three base automorphisms act on double-partial profiles by
the canonical geometric square generators. -/
theorem squareProfile_flipFirst (x : Bool × Bool) :
    (squareProfile x).map squareBaseFlipFirst.toEmbedding =
      squareProfile (squareFlipFirst x) := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;>
    decide

theorem squareProfile_flipSecond (x : Bool × Bool) :
    (squareProfile x).map squareBaseFlipSecond.toEmbedding =
      squareProfile (squareFlipSecond x) := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;>
    decide

theorem squareProfile_swapCoordinates (x : Bool × Bool) :
    (squareProfile x).map squareBaseSwapCoordinates.toEmbedding =
      squareProfile (squareSwapCoordinates x) := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;>
    decide

end EPPAIII.CliqueCovers
