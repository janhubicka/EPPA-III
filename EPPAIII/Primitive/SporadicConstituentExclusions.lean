import EPPAIII.Primitive.G2ConstituentExclusions
import Mathlib.Data.Fin.VecNotation

/-! # The Section 8 constituent check for the sporadic catalogue

The parameter coverage of the published list is an external input.
Each supplied row eliminates all four constituent forms at every root.
The four triangular rows, the Mathieu graph on 77 vertices, and the
Higman–Sims graph have separate arguments.
-/

namespace EPPAIII.Primitive

open SimpleGraph

def CoverDegreeDivisibility (n d : ℕ) : Prop :=
  let m := n / 2
  n % 2 = 0 ∧ (
    (d + 1) ∣ m ∨ ((d + 1) % 2 = 0 ∧ (d + 1) / 2 ∣ m) ∨
    d ∣ m ∨ ((d + 2) % 2 = 0 ∧ (d + 2) / 2 ∣ m) ∨
    d = m - 1 ∨ (d + 1 - m) ∣ m ∨ d = m ∨ (d + 2 - m) ∣ m)

instance (n d : ℕ) : Decidable (CoverDegreeDivisibility n d) := by
  unfold CoverDegreeDivisibility
  infer_instance

/-- Solve each of the eight degree equations for the putative clique size.
This gives the arithmetic test without enumerating the large vertex orders. -/
theorem coverDegree_divisibility {n d : ℕ} (h : CoverDegreeCompatible n d) :
    CoverDegreeDivisibility n d := by
  obtain ⟨hEven, t, ht, hDiv, hDeg⟩ := h
  refine ⟨hEven, ?_⟩
  have hm : 0 < n / 2 := by have := t.isLt; omega
  simp only [coverDegreesAtHalfOrder, Finset.mem_insert, Finset.mem_singleton] at hDeg
  rcases hDeg with h | h | h | h | h | h | h | h
  · exact Or.inl (by simpa only [show d + 1 = t.val by omega] using hDiv)
  · exact Or.inr (Or.inl ⟨by omega,
      by simpa only [show (d + 1) / 2 = t.val by omega] using hDiv⟩)
  · exact Or.inr (Or.inr (Or.inl (by simpa only [h] using hDiv)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,
      by simpa only [show (d + 2) / 2 = t.val by omega] using hDiv⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (by simpa only [show d + 1 - n / 2 = t.val by omega] using hDiv))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (by simpa only [show d + 2 - n / 2 = t.val by omega] using hDiv)))))))

/-- Brouwer and Van Maldeghem's sporadic catalogue, Table 11.3,
omitting the four triangular rows and the graphs on 77 and 100
vertices treated by their own Mathieu and Higman–Sims bounds.
The order-100 Hall–Janko row remains in the table. The orientations
agree with Table 11.3. The codegrees are in the indicated Section 10
descriptions and Table 11.7. -/
def sporadicConstituentParameters : Fin 13 → SRGParameters :=
  ![⟨100, 36, 14, 12⟩,           -- Hall–Janko
    ⟨176, 70, 18, 34⟩,          -- M₂₂
    ⟨253, 112, 36, 60⟩,         -- M₂₃
    ⟨275, 112, 30, 56⟩,         -- McLaughlin
    ⟨1288, 495, 206, 180⟩,      -- dodecad
    ⟨1782, 416, 100, 96⟩,       -- Suzuki
    ⟨2300, 891, 378, 324⟩,      -- Conway Co₂
    ⟨3510, 693, 180, 126⟩,      -- Fi₂₂
    ⟨4060, 1755, 730, 780⟩,     -- Rudvalis
    ⟨14080, 3159, 918, 648⟩,    -- Fi₂₂
    ⟨31671, 3510, 693, 351⟩,    -- Fi₂₃
    ⟨137632, 28431, 6030, 5832⟩, -- Fi₂₃
    ⟨306936, 31671, 3510, 3240⟩] -- Fi₂₄′

/-- Take the catalogue orientation or its complement. -/
def sporadicConstituentParametersOriented (i : Fin 13) (complement : Bool) : SRGParameters :=
  if complement then (sporadicConstituentParameters i).compl else sporadicConstituentParameters i

private theorem sporadic_divisibility_checks :
    ∀ i : Fin 13, ∀ complement side : Bool,
      let p := (sporadicConstituentParametersOriented i complement).constituentProfile side
      0 < p.1 ∧ p.2 < p.1 ∧ ¬ (p.2 + 1) ∣ p.1 ∧ ¬ (p.1 - p.2) ∣ p.1 ∧
        ¬ CoverDegreeDivisibility p.1 p.2 ∧
        ¬ CoverDegreeDivisibility p.1 (p.1 - 1 - p.2) := by
  decide

/-- Every actual rooted constituent of an SRG with one of the displayed
sporadic parameter tuples, in either host orientation, excludes
the four Section 8 forms. -/
theorem sporadic_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (i : Fin 13) (complement : Bool)
    (hSRG : let p := sporadicConstituentParametersOriented i complement
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  obtain ⟨hn, hd, hD, hDCompl, hCover, hCoverCompl⟩ :=
    sporadic_divisibility_checks i complement side
  exact regular_profile_excludes_all_forms
    (constituentGraph_profile H (sporadicConstituentParametersOriented i complement)
      hSRG root side)
    hn hd hD hDCompl (fun h => hCover (coverDegree_divisibility h))
    (fun h => hCoverCompl (coverDegree_divisibility h))

end EPPAIII.Primitive
