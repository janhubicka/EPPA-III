import EPPAIII.CliqueCovers.SingletonChoiceWreath
import EPPAIII.CliqueCovers.OutsideLiftTransport

/-!
# Actual EPPA-induced natural wreath action on the outside half

If a size-one neighbourhood coordinate occurs exactly once in an
outside profile, the orbit saturation theorem canonically identifies
every outside vertex with the index of its singleton coordinate and
the selected vertex there. This is a *specific* bijection with
Fin s × Fin t, not an arbitrary cardinality equivalence.

Using the precise finite-profile transport lemma, an EPPA lift of
every base wreath automorphism acts on these labels by the natural
imprimitive wreath permutation. This supplies the key hypothesis of
EquivariantWreathAssembly without assuming coherent EPPA lifts.
-/

namespace EPPAIII.CliqueCovers

/-- The saturated singleton coordinate labels on the actual outside
vertex subtype, constructed by composing two canonical equivalences. -/
noncomputable def saturatedSingletonOutsideEquiv {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1) :
    (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e} :=
  (singletonChoiceEquiv s t).trans
    (saturatedOutsideChoiceEquiv H e heppa hOrder
      w hw 1 1 hUnique (by simp)).symm

/-- The chosen singleton index and singleton slice of an outside
vertex are exactly its canonical pair label. -/
theorem saturatedSingletonOutsideEquiv_choice {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (x : Fin s × Fin t) :
    extractKChoice
      (finiteNeighbourhoodProfile H e
        (saturatedSingletonOutsideEquiv
          H e heppa hOrder w hw hUnique x).val) 1 =
      (singletonChoiceOfPair x).val := by
  classical
  let E := saturatedOutsideChoiceEquiv H e heppa hOrder
    w hw 1 1 hUnique (by simp)
  let label := saturatedSingletonOutsideEquiv
    H e heppa hOrder w hw hUnique
  have hLabel :
      E (label x) = singletonChoiceEquiv s t x := by
    simp [label, saturatedSingletonOutsideEquiv, E,
      Equiv.trans_apply, Equiv.apply_symm_apply]
  have hActual :=
    saturatedOutsideChoiceEquiv_apply H e heppa hOrder
      w hw 1 1 hUnique (by simp) (label x)
  exact (congrArg Subtype.val hLabel).symm.trans hActual

/-- The canonical pair label determines the *full* singleton
coordinate data needed by the pure wreath equivariance lemma. -/
theorem saturatedSingletonOutsideEquiv_slice {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (x : Fin s × Fin t) :
    kPositions
      (finiteNeighbourhoodProfile H e
        (saturatedSingletonOutsideEquiv
          H e heppa hOrder w hw hUnique x).val) 1 = {x.1} ∧
    profileSlice
      (finiteNeighbourhoodProfile H e
        (saturatedSingletonOutsideEquiv
          H e heppa hOrder w hw hUnique x).val) x.1 = {x.2} := by
  classical
  have hChoice :=
    saturatedSingletonOutsideEquiv_choice
      H e heppa hOrder w hw hUnique x
  constructor
  · exact congrArg Sigma.fst hChoice
  · have hSlice := congrArg
      (fun (C : Σ R : Finset (Fin s),
        ∀ i : Fin s, i ∈ R → Finset (Fin t)) =>
          if hi : x.1 ∈ C.1 then C.2 x.1 hi else ∅) hChoice
    simpa [extractKChoice, singletonChoiceOfPair] using hSlice

/-- Every base wreath automorphism has an actual outside graph
automorphism acting by the *natural* wreath permutation in the
canonical singleton labels. The extension is chosen only once per
base permutation; no coherent choice is assumed. -/
theorem eppa_singleton_outside_has_natural_wreath_action {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    ∃ q : Equiv.Perm {u : W // u ∈ finiteOutside e},
      IsGraphAutomorphism (outsideInducedGraph H e) q ∧
      ∀ x : Fin s × Fin t,
        q (saturatedSingletonOutsideEquiv
            H e heppa hOrder w hw hUnique x) =
          saturatedSingletonOutsideEquiv
            H e heppa hOrder w hw hUnique
              (((outerPermutation outer).trans
                (innerPermutation inner)) x) := by
  classical
  let p : Equiv.Perm (Fin s × Fin t) :=
    (outerPermutation outer).trans (innerPermutation inner)
  obtain ⟨q, hq, hCompat⟩ :=
    eppa_lifts_total (cliqueUnion s t) H e heppa
      p (wreathPermutation_aut outer inner)
  refine ⟨outsideLiftPermutation e p q hCompat,
    outsideLiftPermutation_graphAut H e p q hCompat hq, ?_⟩
  intro x
  let label := saturatedSingletonOutsideEquiv
    H e heppa hOrder w hw hUnique
  let u := label x
  let v := label (p x)
  have hU := saturatedSingletonOutsideEquiv_slice
    H e heppa hOrder w hw hUnique x
  have hWreath :
      extractKChoice (finiteNeighbourhoodProfile H e (q u.val)) 1 =
        (singletonChoiceOfPair (p x)).val := by
    rw [finite_profile_wreath_lift H e u.val
      outer inner q hq hCompat]
    exact extractKChoice_wreath_singleton
      (finiteNeighbourhoodProfile H e u.val)
      x.1 x.2 hU.1 hU.2 outer inner
  have hV := saturatedSingletonOutsideEquiv_choice
    H e heppa hOrder w hw hUnique (p x)
  have hOut : (outsideLiftPermutation e p q hCompat u).val =
      q u.val := rfl
  have hEq : (outsideLiftPermutation e p q hCompat u).val = v.val := by
    apply (eppa_saturated_outside_choice_injective
      H e heppa hOrder w hw 1 1 hUnique (by simp))
        (outsideLiftPermutation e p q hCompat u).property v.property
    rw [hOut]
    exact hWreath.trans hV.symm
  exact Subtype.ext hEq

end EPPAIII.CliqueCovers
