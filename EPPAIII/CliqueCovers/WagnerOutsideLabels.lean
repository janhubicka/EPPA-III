import EPPAIII.CliqueCovers.WagnerSquareChoiceLabels
import EPPAIII.CliqueCovers.OutsideLiftTransport

/-!
# The four actual outside vertices in the Wagner exceptional orbit

When s=t=2 and an outside neighbourhood has two size-one slices,
the orbit lower bound saturates the four outside vertices. The
canonical equivalence of actual outside vertices with admissible
two-singleton choices, composed with the explicit Bool×Bool choice
equivalence, gives a canonical label of every outside vertex by its
two selected base points. No coherent EPPA lift is needed.

The final two slice identities are the interface for proving the
actual outside action of the three generating base permutations.
-/

namespace EPPAIII.CliqueCovers

/-- The double-partial profile orbit is exactly large enough to
exhaust the four outside vertices. -/
theorem wagner_square_choice_saturation :
    Nat.choose 2 2 * (Nat.choose 2 1)^2 = 2 * 2 := by
  decide

/-- A canonical four-corner labelling of every outside vertex. -/
noncomputable def saturatedWagnerOutsideEquiv
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2) :
    (Bool × Bool) ≃ {u : W // u ∈ finiteOutside e} :=
  squareChoiceEquiv.trans
    (saturatedOutsideChoiceEquiv H e heppa hOrder w hw 2 1
      hBoth wagner_square_choice_saturation).symm

/-- The actual extracted choice at corner x is exactly its
formal pair of singleton base points. -/
theorem saturatedWagnerOutsideEquiv_choice
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (x : Bool × Bool) :
    extractKChoice (finiteNeighbourhoodProfile H e
      (saturatedWagnerOutsideEquiv H e heppa hOrder
        w hw hBoth x).val) 1 = (squareChoiceOfPair x).val := by
  classical
  let E := saturatedOutsideChoiceEquiv H e heppa hOrder
    w hw 2 1 hBoth wagner_square_choice_saturation
  let label := saturatedWagnerOutsideEquiv
    H e heppa hOrder w hw hBoth
  have hLabel : E (label x) = squareChoiceEquiv x := by
    simp [label, saturatedWagnerOutsideEquiv, E,
      Equiv.trans_apply, Equiv.apply_symm_apply]
  have hActual := saturatedOutsideChoiceEquiv_apply
    H e heppa hOrder w hw 2 1 hBoth
      wagner_square_choice_saturation (label x)
  exact hActual.symm.trans (congrArg Subtype.val hLabel)

/-- Each canonical outside corner has the expected singleton
neighbourhood in the first designated clique. -/
theorem saturatedWagnerOutsideEquiv_first
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (x : Bool × Bool) :
    profileSlice (finiteNeighbourhoodProfile H e
      (saturatedWagnerOutsideEquiv H e heppa hOrder
        w hw hBoth x).val) (0 : Fin 2) =
      {finTwoEquiv.symm x.1} := by
  classical
  have hChoice := saturatedWagnerOutsideEquiv_choice
    H e heppa hOrder w hw hBoth x
  have hPositions :
      kPositions (finiteNeighbourhoodProfile H e
        (saturatedWagnerOutsideEquiv H e heppa hOrder
          w hw hBoth x).val) 1 = Finset.univ := by
    have hPos := congrArg Sigma.fst hChoice
    change kPositions (finiteNeighbourhoodProfile H e
      (saturatedWagnerOutsideEquiv H e heppa hOrder
        w hw hBoth x).val) 1 = Finset.univ at hPos
    exact hPos
  have hSlice := congrArg
    (fun C : Σ R : Finset (Fin 2),
      ∀ i : Fin 2, i ∈ R → Finset (Fin 2) =>
        if hi : (0 : Fin 2) ∈ C.1 then C.2 0 hi else ∅) hChoice
  simpa [extractKChoice, squareChoiceOfPair,
    admissibleChoiceSlice, hPositions] using hSlice

/-- Same, for the second designated clique. -/
theorem saturatedWagnerOutsideEquiv_second
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (x : Bool × Bool) :
    profileSlice (finiteNeighbourhoodProfile H e
      (saturatedWagnerOutsideEquiv H e heppa hOrder
        w hw hBoth x).val) (1 : Fin 2) =
      {finTwoEquiv.symm x.2} := by
  classical
  have hChoice := saturatedWagnerOutsideEquiv_choice
    H e heppa hOrder w hw hBoth x
  have hPositions :
      kPositions (finiteNeighbourhoodProfile H e
        (saturatedWagnerOutsideEquiv H e heppa hOrder
          w hw hBoth x).val) 1 = Finset.univ := by
    have hPos := congrArg Sigma.fst hChoice
    change kPositions (finiteNeighbourhoodProfile H e
      (saturatedWagnerOutsideEquiv H e heppa hOrder
        w hw hBoth x).val) 1 = Finset.univ at hPos
    exact hPos
  have hSlice := congrArg
    (fun C : Σ R : Finset (Fin 2),
      ∀ i : Fin 2, i ∈ R → Finset (Fin 2) =>
        if hi : (1 : Fin 2) ∈ C.1 then C.2 1 hi else ∅) hChoice
  simpa [extractKChoice, squareChoiceOfPair,
    admissibleChoiceSlice, hPositions] using hSlice

end EPPAIII.CliqueCovers
