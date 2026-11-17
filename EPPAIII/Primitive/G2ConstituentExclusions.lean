import EPPAIII.Primitive.ConstituentProfileScreen
import EPPAIII.Primitive.SmallConstituentGraphScreen

/-! # Numerical constituent exclusions for the two G₂ graphs -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem screen_regular_profile {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n d : ℕ} (hProfile : HasRegularProfile G (n, d))
    (hn : 0 < n) (hd : d < n) (hUnion : ¬ (d + 1) ∣ n) (hUnionCompl : ¬ (n - d) ∣ n)
    (hCover : ¬ CoverDegreeCompatible n d) (hCoverCompl : ¬ CoverDegreeCompatible n (n - 1 - d)) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  have hCard : Fintype.card V = n := Nat.card_eq_fintype_card.symm.trans hProfile.1
  have hDegree : G.IsRegularOfDegree d := by
    intro x
    rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hProfile.2 x
  obtain ⟨hClique, hCoClique⟩ :=
    regular_profile_excludes_cliqueUnion G hn hd hCard hDegree hUnion hUnionCompl
  obtain ⟨hCover, hCoCover⟩ :=
    regular_profile_excludes_cover G hn hCard hDegree hCover hCoverCompl
  exact ⟨hClique, hCoClique, hCover, hCoCover⟩

/-- The Fano-based order-36 G₂(2) graph has neither a clique-union nor a cover
constituent in either orientation. Only its published SRG parameters are needed. -/
theorem g2Two_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hSRG : H.IsSRGWith 36 14 4 6)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · exact screen_regular_profile (n := 14) (d := 4)
      (constituentGraph_profile H ⟨36, 14, 4, 6⟩ hSRG root false)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact screen_regular_profile (n := 21) (d := 8)
      (constituentGraph_profile H ⟨36, 14, 4, 6⟩ hSRG root true)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The order-416 G₂(4) graph has neither a clique-union nor a cover
constituent in either orientation. Only its published SRG parameters are needed. -/
theorem g2Four_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hSRG : H.IsSRGWith 416 100 36 20)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · exact screen_regular_profile (n := 100) (d := 36)
      (constituentGraph_profile H ⟨416, 100, 36, 20⟩ hSRG root false)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact screen_regular_profile (n := 315) (d := 80)
      (constituentGraph_profile H ⟨416, 100, 36, 20⟩ hSRG root true)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
/-- The binary half-spin graph has neither a clique-union nor a cover
constituent in either orientation. -/
theorem binary_halfSpin_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (hSRG : H.IsSRGWith 2295 310 85 35)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · exact screen_regular_profile (n := 310) (d := 85)
      (constituentGraph_profile H ⟨2295, 310, 85, 35⟩ hSRG root false)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact screen_regular_profile (n := 1984) (d := 275)
      (constituentGraph_profile H ⟨2295, 310, 85, 35⟩ hSRG root true)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end EPPAIII.Primitive
