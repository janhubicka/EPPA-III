import EPPAIII.CliqueCovers.CoSingletonChoiceWreath
import EPPAIII.CliqueCovers.OutsideLiftTransport

/-!
# Genuine EPPA natural wreath action on co-singleton outside labels

The co-singleton coordinate is labelled by the unique omitted point.
At saturation, each outside vertex has a unique such label. Actual EPPA
lifts act on it by the natural imprimitive S_t wr S_s permutation, since
inner permutations carry omitted points forward and outer permutations
move the selected coordinate.

No preselected outside clique partition or coherent EPPA lifts are used.
-/

namespace EPPAIII.CliqueCovers

/-- The size-(t-1) choice space has exactly s*t labels whenever
t>0. This includes t=1 but the one-partial application has t≥2. -/
theorem coSingletonChoice_saturation (s t : ℕ) (ht : 0 < t) :
    Nat.choose s 1 * (Nat.choose t (t - 1))^1 = s * t := by
  have hComplement : t - (t - 1) = 1 := by omega
  have hChoose : Nat.choose t (t - 1) = t := by
    calc
      Nat.choose t (t - 1) =
          Nat.choose t (t - (t - 1)) :=
        (Nat.choose_symm (Nat.sub_le t 1)).symm
      _ = Nat.choose t 1 := by rw [hComplement]
      _ = t := Nat.choose_one_right t
  simp [hChoose]

/-- Canonical omitted-point labels of all vertices outside G,
when the profile contains exactly one size-(t-1) coordinate. -/
noncomputable def saturatedCoSingletonOutsideEquiv {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (ht : 0 < t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1) :
    (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e} :=
  (coSingletonChoiceEquiv s t ht).trans
    (saturatedOutsideChoiceEquiv H e heppa hOrder
      w hw 1 (t - 1) hUnique
      (coSingletonChoice_saturation s t ht)).symm

/-- Under this canonical bijection, extraction of the selected
co-singleton coordinate gives exactly its omitted-point pair. -/
theorem saturatedCoSingletonOutsideEquiv_choice {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (ht : 0 < t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (x : Fin s × Fin t) :
    extractKChoice
      (finiteNeighbourhoodProfile H e
        (saturatedCoSingletonOutsideEquiv
          H e heppa hOrder ht w hw hUnique x).val) (t - 1) =
      (coSingletonChoiceOfPair x).val := by
  classical
  let E := saturatedOutsideChoiceEquiv H e heppa hOrder
    w hw 1 (t - 1) hUnique
      (coSingletonChoice_saturation s t ht)
  let label := saturatedCoSingletonOutsideEquiv
    H e heppa hOrder ht w hw hUnique
  have hLabel :
      E (label x) = coSingletonChoiceEquiv s t ht x := by
    simp [label, saturatedCoSingletonOutsideEquiv, E,
      Equiv.trans_apply, Equiv.apply_symm_apply]
  have hActual :=
    saturatedOutsideChoiceEquiv_apply H e heppa hOrder
      w hw 1 (t - 1) hUnique
        (coSingletonChoice_saturation s t ht) (label x)
  exact hActual.symm.trans (congrArg Subtype.val hLabel)

/-- The actual co-singleton profile at a labelled outside vertex
omits exactly the second coordinate of the label. -/
theorem saturatedCoSingletonOutsideEquiv_slice {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (ht : 0 < t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (x : Fin s × Fin t) :
    kPositions
      (finiteNeighbourhoodProfile H e
        (saturatedCoSingletonOutsideEquiv
          H e heppa hOrder ht w hw hUnique x).val) (t - 1) = {x.1} ∧
    profileSlice
      (finiteNeighbourhoodProfile H e
        (saturatedCoSingletonOutsideEquiv
          H e heppa hOrder ht w hw hUnique x).val) x.1 =
          (({x.2} : Finset (Fin t))ᶜ) := by
  classical
  have hChoice :=
    saturatedCoSingletonOutsideEquiv_choice
      H e heppa hOrder ht w hw hUnique x
  have hPositions :
      kPositions
        (finiteNeighbourhoodProfile H e
          (saturatedCoSingletonOutsideEquiv
            H e heppa hOrder ht w hw hUnique x).val) (t - 1) = {x.1} :=
    congrArg Sigma.fst hChoice
  constructor
  · exact hPositions
  · have hSlice := congrArg
      (fun (C : Σ R : Finset (Fin s),
        ∀ i : Fin s, i ∈ R → Finset (Fin t)) =>
          if hi : x.1 ∈ C.1 then C.2 x.1 hi else ∅) hChoice
    simpa [extractKChoice, coSingletonChoiceOfPair,
      hPositions] using hSlice

/-- Every wreath automorphism of the base has an actual automorphism
of the outside induced graph acting as the NATURAL wreath permutation
in its canonical co-singleton omitted-point coordinates. -/
theorem eppa_cosingleton_outside_has_natural_wreath_action {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (ht : 0 < t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    ∃ q : Equiv.Perm {u : W // u ∈ finiteOutside e},
      IsGraphAutomorphism (outsideInducedGraph H e) q ∧
      ∀ x : Fin s × Fin t,
        q (saturatedCoSingletonOutsideEquiv
            H e heppa hOrder ht w hw hUnique x) =
          saturatedCoSingletonOutsideEquiv
            H e heppa hOrder ht w hw hUnique
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
  let label := saturatedCoSingletonOutsideEquiv
    H e heppa hOrder ht w hw hUnique
  let u := label x
  let v := label (p x)
  have hU := saturatedCoSingletonOutsideEquiv_slice
    H e heppa hOrder ht w hw hUnique x
  have hWreath :
      extractKChoice
        (finiteNeighbourhoodProfile H e (q u.val)) (t - 1) =
        (coSingletonChoiceOfPair (p x)).val := by
    rw [finite_profile_wreath_lift H e u.val
      outer inner q hq hCompat]
    exact extractKChoice_wreath_coSingleton
      (finiteNeighbourhoodProfile H e u.val)
      x.1 x.2 hU.1 hU.2 outer inner
  have hV := saturatedCoSingletonOutsideEquiv_choice
    H e heppa hOrder ht w hw hUnique (p x)
  have hOut : (outsideLiftPermutation e p q hCompat u).val =
      q u.val := rfl
  have hEq : (outsideLiftPermutation e p q hCompat u).val = v.val := by
    apply (eppa_saturated_outside_choice_injective
      H e heppa hOrder w hw 1 (t - 1) hUnique
        (coSingletonChoice_saturation s t ht))
        (outsideLiftPermutation e p q hCompat u).property v.property
    rw [hOut]
    exact hWreath.trans hV.symm
  exact Subtype.ext hEq

end EPPAIII.CliqueCovers
