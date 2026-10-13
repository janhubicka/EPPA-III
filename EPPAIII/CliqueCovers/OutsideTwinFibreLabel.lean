import EPPAIII.CliqueCovers.OutsideTwinIndexBudget
import EPPAIII.CliqueCovers.OutsideTwinClasses
import EPPAIII.CliqueCovers.ClosedTwinClasses

/-!
# Outside vertex labels from quotient classes and their fibres

Suppose the outside closed-twin quotient has s classes and each such
class has been enumerated by Fin t. Then these enumerations glue into
a bijection Fin s × Fin t ≃ H\G. In its i-th fibre every pair of
vertices has the same closed neighbourhood.

The lemma does not invent any labelling: it constructs one from
the explicit finite equivalences of the quotient classes and their
fibres, and proves exact surjectivity and injectivity. The remaining
zero-partial classification uses the already verified spanning-edge
theorem to show that this labelling makes H\G exactly sK_t.

No automorphism-group coherence or outside clique partition is
assumed. The hypotheses about the quotient are separate inputs.
-/

namespace EPPAIII.CliqueCovers

/-- Glue outside quotient-class indices and within-class
enumerations into a genuine equivalence of the entire outside half
with Fin s × Fin t. Its fibres consist of true twins. -/
theorem exists_outside_twin_fibre_label {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) i).card = t)
    (a : Fin t)
    (hSize : ∀ i : Fin s, (closedTwinClass H (e (i,a))).card = t)
    [Fintype (ClosedTwinQuotient H)]
    (hCount : (outsideTwinQuotientClasses H e a).card = s)
    (fibreEquiv :
      ∀ z : {q : ClosedTwinQuotient H //
        q ∈ outsideTwinQuotientClasses H e a},
        Fin t ≃ {w : W // Quotient.mk (closedTwinSetoid H) w = z.val}) :
    ∃ label : (Fin s × Fin t) ≃ {w : W // w ∈ finiteOutside e},
      ∀ (i : Fin s) (b c : Fin t),
        SameClosedNeighbourhood H (label (i,b)).val (label (i,c)).val := by
  classical
  let Q := {q : ClosedTwinQuotient H //
      q ∈ outsideTwinQuotientClasses H e a}
  have hQ : Fintype.card Q = s := by
    change Fintype.card ↥(outsideTwinQuotientClasses H e a) = s
    simpa only [Fintype.card_coe] using hCount
  let key : Fin s ≃ Q := (Fintype.equivFinOfCardEq hQ).symm
  let g : (Fin s × Fin t) →
      {w : W // w ∈ finiteOutside e} := fun x => by
    let v := (fibreEquiv (key x.1) x.2).val
    have hvClass :
        Quotient.mk (closedTwinSetoid H) v = (key x.1).val :=
      (fibreEquiv (key x.1) x.2).property
    have hNotSelected :
        (key x.1).val ∉
          (selectedTwinClasses H e a : Set (ClosedTwinQuotient H)) :=
      (Finset.mem_sdiff.mp (key x.1).property).2
    have hvNotSelected :
        Quotient.mk (closedTwinSetoid H) v ∉
          (selectedTwinClasses H e a : Set (ClosedTwinQuotient H)) := by
      rw [hvClass]
      exact hNotSelected
    have hvOutside : v ∉ Set.range e :=
      nonselected_quotient_implies_outside
        H e he hNoPartial a v hvNotSelected
    exact ⟨v, by simpa [finiteOutside] using hvOutside⟩
  have hQuot (x : Fin s × Fin t) :
      Quotient.mk (closedTwinSetoid H) (g x).val = (key x.1).val := by
    change Quotient.mk (closedTwinSetoid H)
      (fibreEquiv (key x.1) x.2).val = (key x.1).val
    exact (fibreEquiv (key x.1) x.2).property
  have hInj : Function.Injective g := by
    intro x y h
    have hValue : (g x).val = (g y).val := congrArg Subtype.val h
    have hClasses : (key x.1).val = (key y.1).val := by
      calc
        (key x.1).val =
          Quotient.mk (closedTwinSetoid H) (g x).val := (hQuot x).symm
        _ = Quotient.mk (closedTwinSetoid H) (g y).val :=
          congrArg (Quotient.mk (closedTwinSetoid H)) hValue
        _ = (key y.1).val := hQuot y
    have hIndex : x.1 = y.1 :=
      key.injective (Subtype.ext hClasses)
    rcases x with ⟨i,b⟩
    rcases y with ⟨j,c⟩
    dsimp at hIndex
    subst j
    have hFibre :
        fibreEquiv (key i) b = fibreEquiv (key i) c := by
      apply Subtype.ext
      exact hValue
    have hbc : b = c := (fibreEquiv (key i)).injective hFibre
    exact Prod.ext rfl hbc
  have hSurj : Function.Surjective g := by
    intro w
    have hwOut : w.val ∉ Set.range e := by
      simpa [finiteOutside] using w.property
    have hNotSelected :
        Quotient.mk (closedTwinSetoid H) w.val ∉
          (selectedTwinClasses H e a : Set (ClosedTwinQuotient H)) :=
      outside_quotient_not_selected
        H e he hNoPartial a hSize w.val hwOut
    have hOutClass :
        Quotient.mk (closedTwinSetoid H) w.val ∈
          outsideTwinQuotientClasses H e a :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hNotSelected⟩
    let z : Q := ⟨Quotient.mk (closedTwinSetoid H) w.val, hOutClass⟩
    let i : Fin s := key.symm z
    have hIndex : key i = z := key.apply_symm_apply z
    have hClass :
        Quotient.mk (closedTwinSetoid H) w.val = (key i).val :=
      (congrArg Subtype.val hIndex).symm
    let u : {v : W // Quotient.mk (closedTwinSetoid H) v = (key i).val} :=
      ⟨w.val,hClass⟩
    let b : Fin t := (fibreEquiv (key i)).symm u
    have hFibre : fibreEquiv (key i) b = u :=
      (fibreEquiv (key i)).apply_symm_apply u
    refine ⟨(i,b), ?_⟩
    apply Subtype.ext
    change (fibreEquiv (key i) b).val = w.val
    exact congrArg Subtype.val hFibre
  let label : (Fin s × Fin t) ≃ {w : W // w ∈ finiteOutside e} :=
    Equiv.ofBijective g ⟨hInj,hSurj⟩
  refine ⟨label, ?_⟩
  intro i b c
  have hb : Quotient.mk (closedTwinSetoid H) (label (i,b)).val =
      (key i).val := hQuot (i,b)
  have hc : Quotient.mk (closedTwinSetoid H) (label (i,c)).val =
      (key i).val := hQuot (i,c)
  exact Quotient.exact (hb.trans hc.symm)

end EPPAIII.CliqueCovers
