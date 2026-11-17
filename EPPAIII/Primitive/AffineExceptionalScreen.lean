import EPPAIII.Primitive.SporadicConstituentExclusions

/-! # Numerical screen for the extraspecial and exceptional affine families -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- The parameter rows of the affine catalogue passing the numerical
exclusion in both constituents. The finite list is drawn from
Brouwer–Van Maldeghem Tables 11.5 and 11.6 and Theorems 11.4.3 and 11.4.4. -/
def affineExceptionalExcludedParameters : Fin 25 → SRGParameters :=
  ![⟨289, 96, 35, 30⟩,
    ⟨361, 144, 59, 56⟩,
    ⟨729, 104, 31, 12⟩,
    ⟨841, 168, 47, 30⟩,
    ⟨961, 240, 71, 56⟩,
    ⟨625, 240, 95, 90⟩,
    ⟨6561, 1440, 351, 306⟩,
    ⟨243, 110, 37, 60⟩,
    ⟨256, 45, 16, 6⟩,
    ⟨256, 102, 38, 42⟩,
    ⟨625, 144, 43, 30⟩,
    ⟨729, 224, 61, 72⟩,
    ⟨2048, 759, 310, 264⟩,
    ⟨2401, 720, 229, 210⟩,
    ⟨4096, 1575, 614, 600⟩,
    ⟨531441, 65520, 8559, 8010⟩,
    ⟨256, 75, 26, 20⟩,
    ⟨961, 360, 139, 132⟩,
    ⟨1681, 480, 149, 132⟩,
    ⟨2401, 960, 389, 380⟩,
    ⟨4096, 315, 74, 20⟩,
    ⟨5041, 840, 179, 132⟩,
    ⟨6241, 1560, 419, 380⟩,
    ⟨7921, 2640, 899, 870⟩,
    ⟨15625, 744, 143, 30⟩]

/-- The same graph in either host orientation. -/
def affineExceptionalExcludedParametersOriented (i : Fin 25) (complement : Bool) :
    SRGParameters :=
  if complement then (affineExceptionalExcludedParameters i).compl
  else affineExceptionalExcludedParameters i

private theorem affineExceptional_divisibility_checks :
    ∀ i : Fin 25, ∀ complement side : Bool,
      let p := (affineExceptionalExcludedParametersOriented i complement).constituentProfile side
      0 < p.1 ∧ p.2 < p.1 ∧ ¬ (p.2 + 1) ∣ p.1 ∧ ¬ (p.1 - p.2) ∣ p.1 ∧
        ¬ CoverDegreeDivisibility p.1 p.2 ∧
        ¬ CoverDegreeDivisibility p.1 (p.1 - 1 - p.2) := by
  decide

/-- Every actual subconstituent of an SRG with a screened affine parameter
tuple fails all four Section 8 forms, in either orientation. -/
theorem affineExceptional_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (i : Fin 25) (complement : Bool)
    (hSRG : let p := affineExceptionalExcludedParametersOriented i complement
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  obtain ⟨hn, hd, hD, hDCompl, hCover, hCoverCompl⟩ :=
    affineExceptional_divisibility_checks i complement side
  exact regular_profile_excludes_all_forms
    (constituentGraph_profile H (affineExceptionalExcludedParametersOriented i complement)
      hSRG root side)
    hn hd hD hDCompl (fun h => hCover (coverDegree_divisibility h))
    (fun h => hCoverCompl (coverDegree_divisibility h))

end EPPAIII.Primitive
