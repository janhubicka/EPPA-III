import EPPAIII.CliqueCovers.ZeroPartialOutsideConclusion
import EPPAIII.CliqueCovers.OutsideMaskAction
import EPPAIII.CliqueCovers.FullMaskNormalForms

/-!
# Every fixed-size full-clique mask occurs among the outside twin fibres

An outside labelling Fin s × Fin t furnished by the true-twin
quotient carries a canonically associated family of s masks,
one mask per outside true-twin class. Since all vertices in the
same fibre are true twins, every outside vertex has one of these
masks, and the mask does not depend on the choice of a vertex
inside its fibre.

An EPPA extension of any permutation of the distinguished K_t's
realises every permutation image of an actual outside mask.
Consequently, if the s masks all have the same cardinality r,
they cover every r-subset of Fin s. In particular choose(s,r)≤s,
and the family is empty/full or can be reindexed to the
singleton/co-singleton normal form.

This is the full group-action part of the zero-partial matrix
classification. Proving uniformity of the mask size r from host
vertex-transitivity (via regularity of the 2s-vertex true-twin
quotient) is an independent last graph-level obligation.
-/

namespace EPPAIII.CliqueCovers

/-- One full-clique adjacency mask for each of the s outside true-twin
classes. The within-class coordinate a is irrelevant by twinhood. -/
noncomputable def outsideMaskFamily {s t : ℕ} {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (a : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e}) :
    Fin s → Finset (Fin s) :=
  fun j => outsideIndexMask H e a (label (j,a)).val

/-- Every actual outside vertex has the mask of one labelled true-twin
fibre. This follows from the canonical quotient labelling, not from
transitivity of the host automorphism action on the outside half. -/
theorem outside_mask_in_twin_family {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (a : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (b c : Fin t),
      SameClosedNeighbourhood H (label (i,b)).val (label (i,c)).val)
    (u : W) (hu : u ∉ Set.range e) :
    ∃ j : Fin s,
      outsideMaskFamily H e a label j = outsideIndexMask H e a u := by
  classical
  have huFin : u ∈ finiteOutside e := by
    simpa [finiteOutside] using hu
  let x : Fin s × Fin t := label.symm ⟨u,huFin⟩
  have huLabel : (label x).val = u := by
    simp [x]
  have hTwins :
      SameClosedNeighbourhood H (label (x.1,a)).val u := by
    have h := hFibre x.1 a x.2
    simpa only [huLabel] using h
  have hAnchor : (label (x.1,a)).val ∉ Set.range e := by
    simpa [finiteOutside] using (label (x.1,a)).property
  refine ⟨x.1, ?_⟩
  exact outsideIndexMask_eq_of_closed_twins
    H e a (label (x.1,a)).val u hAnchor hu hTwins

/-- Every image of an actual outside mask under the whole
symmetric group appears as the mask of one outside twin class. -/
theorem eppa_outside_twin_mask_family_covers_orbit {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (a : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (b c : Fin t),
      SameClosedNeighbourhood H (label (i,b)).val (label (i,c)).val)
    (i : Fin s)
    (R : Finset (Fin s))
    (hOrbit : R ∈ outerMaskOrbit (outsideMaskFamily H e a label i)) :
    ∃ j : Fin s, outsideMaskFamily H e a label j = R := by
  classical
  have hwOutside : (label (i,a)).val ∉ Set.range e := by
    simpa [finiteOutside] using (label (i,a)).property
  obtain ⟨u,hu,hMask⟩ :=
    eppa_outer_mask_orbit_realized H e heppa a
      (label (i,a)).val hwOutside R hOrbit
  obtain ⟨j,hj⟩ :=
    outside_mask_in_twin_family H e a label hFibre u hu
  exact ⟨j,hj.trans hMask⟩

/-- If all s outside true-twin masks have the same cardinality r,
the EPPA orbit of any one of them contains every r-subset and is
realised among these s classes. -/
theorem eppa_outside_mask_family_covers_all_fixed_size {s t r : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (a : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (b c : Fin t),
      SameClosedNeighbourhood H (label (i,b)).val (label (i,c)).val)
    (hs : 0 < s)
    (hCard : ∀ i : Fin s, (outsideMaskFamily H e a label i).card = r)
    (R : Finset (Fin s)) (hR : R.card = r) :
    ∃ j : Fin s, outsideMaskFamily H e a label j = R := by
  let i0 : Fin s := ⟨0,hs⟩
  have hOrbit : R ∈ outerMaskOrbit (outsideMaskFamily H e a label i0) := by
    rw [outerMaskOrbit_eq_powersetCard, hCard i0]
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hR⟩
  exact eppa_outside_twin_mask_family_covers_orbit
    H e heppa a label hFibre i0 R hOrbit

/-- The genuine outside masks have precisely the four normal forms
whenever their sizes are uniform. The remaining regularity argument
to obtain this uniformity is intentionally kept as a separate
obligation, rather than hidden in the theorem's hypotheses. -/
theorem eppa_outside_twin_mask_family_four_forms {s t r : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (a : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (b c : Fin t),
      SameClosedNeighbourhood H (label (i,b)).val (label (i,c)).val)
    (hs : 0 < s)
    (hCard : ∀ i : Fin s, (outsideMaskFamily H e a label i).card = r) :
    (r = 0 ∧ ∀ i : Fin s, outsideMaskFamily H e a label i = ∅) ∨
    (r = 1 ∧ ∃ p : Equiv.Perm (Fin s),
      ∀ i : Fin s, outsideMaskFamily H e a label (p i) = {i}) ∨
    (r + 1 = s ∧ ∃ p : Equiv.Perm (Fin s),
      ∀ i : Fin s, outsideMaskFamily H e a label (p i) =
        (Finset.univ : Finset (Fin s)).erase i) ∨
    (r = s ∧ ∀ i : Fin s,
      outsideMaskFamily H e a label i =
        (Finset.univ : Finset (Fin s))) := by
  classical
  let mask := outsideMaskFamily H e a label
  have hCover : ∀ R : Finset (Fin s), R.card = r →
      ∃ i : Fin s, mask i = R := by
    intro R hR
    exact eppa_outside_mask_family_covers_all_fixed_size
      H e heppa a label hFibre hs hCard R hR
  have hSub :
      ((Finset.univ : Finset (Fin s)).powersetCard r) ⊆
        (Finset.univ : Finset (Fin s)).image mask := by
    intro R hR
    obtain ⟨j,hj⟩ := hCover R (Finset.mem_powersetCard.mp hR).2
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
  have hBound : Nat.choose s r ≤ s := by
    calc
      Nat.choose s r =
          ((Finset.univ : Finset (Fin s)).powersetCard r).card := by
            simp
      _ ≤ ((Finset.univ : Finset (Fin s)).image mask).card :=
        Finset.card_le_card hSub
      _ ≤ s := by
        simpa using
          (Finset.card_image_le (s := (Finset.univ : Finset (Fin s)))
            (f := mask))
  exact full_mask_family_four_normal_forms mask hs hCard hCover hBound

end EPPAIII.CliqueCovers
