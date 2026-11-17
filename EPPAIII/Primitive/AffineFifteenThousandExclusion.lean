import EPPAIII.Primitive.AffineExceptionalRefinements
import EPPAIII.Primitive.SporadicConstituentExclusions
import EPPAIII.Primitive.Subconstituents

/-! # The exceptional Hall–Janko affine row on 15625 vertices -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem local_cover_candidate {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (h : H.IsSRGWith 15625 7560 3655 3660) (root : V)
    {s t : ℕ} {X : CrossType} {Y : Bool}
    (φ : localGraph H root ≃g (coverGraph s t X Y)ᶜ) :
    s = 30 ∧ t = 126 ∧ Y = true := by
  classical
  have hp := constituentGraph_profile H ⟨15625, 7560, 3655, 3660⟩ h root false
  have hCard : Fintype.card (H.neighborSet root) = 7560 :=
    Nat.card_eq_fintype_card.symm.trans hp.1
  have hReg : (localGraph H root).IsRegularOfDegree 3655 := by
    intro x
    rw [← (localGraph H root).card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hp.2 x
  have hSize : Fintype.card (CoverVertex s t) = 7560 := φ.card_eq.symm.trans hCard
  obtain ⟨⟨_, i, a⟩⟩ := Fintype.card_pos_iff.mp (by rw [hSize]; decide :
    0 < Fintype.card (CoverVertex s t))
  have hs : 0 < s := i.isLt.pos
  have ht : 0 < t := a.isLt.pos
  have hHalf : s * t = 3780 := by
    rw [coverVertex_card, Nat.mul_assoc] at hSize
    omega
  have htLe : t ≤ 3780 := by
    simpa only [Nat.one_mul, hHalf] using Nat.mul_le_mul_right t (show 1 ≤ s by omega)
  have htDvd : t ∣ 3780 := ⟨s, by rw [← hHalf, Nat.mul_comm]⟩
  have hOff : (s - 1) * t = 3780 - t := by rw [Nat.sub_mul, Nat.one_mul, hHalf]
  have hDeg := φ.symm.degree_eq (left i a)
  rw [hReg, degree_compl, hSize, coverGraph_left_degree X Y i a] at hDeg
  have htEq : t = 126 ∧ Y = true := by
    cases X <;> cases Y <;> simp [coverDiagonalDegree, hOff] at hDeg ⊢ <;>
      first
      | omega
      | have ht1953 : t = 1953 := by omega
        subst t
        exact False.elim ((by decide : ¬ 1953 ∣ 3780) htDvd)
      | have ht125 : t = 125 := by omega
        subst t
        exact False.elim ((by decide : ¬ 125 ∣ 3780) htDvd)
  refine ⟨?_, htEq.1, htEq.2⟩
  rw [htEq.1] at hHalf
  omega

/-- Both rooted constituents of the exceptional Hall–Janko affine model
fail the four permitted Section 8 forms. Only the SRG tuple is needed. -/
theorem affine_15625_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 15625 7560 3655 3660)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · have hp := constituentGraph_profile H ⟨15625, 7560, 3655, 3660⟩ h root false
    let G := localGraph H root
    have hCard : Fintype.card (H.neighborSet root) = 7560 :=
      Nat.card_eq_fintype_card.symm.trans hp.1
    have hReg : G.IsRegularOfDegree 3655 := by
      intro x
      rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      exact hp.2 x
    obtain ⟨hClique, hComplClique⟩ := regular_profile_excludes_cliqueUnion G
      (by decide) (by decide) hCard hReg (by decide) (by decide)
    refine ⟨hClique, hComplClique, ?_, ?_⟩
    · intro s t X Y
      exact ⟨fun φ => (by decide : ¬ CoverDegreeDivisibility 7560 3655)
        (coverDegree_divisibility (coverDegreeCompatible_of_iso (by decide) hCard hReg φ))⟩
    · intro s t X Y
      refine ⟨fun φ => ?_⟩
      obtain ⟨rfl, rfl, rfl⟩ := local_cover_candidate H h root φ
      let inclusion : G ↪g H := {
        toEmbedding := Function.Embedding.subtype _
        map_rel_iff' := Iff.rfl }
      exact affine_15625_no_complemented_cover H h X (inclusion.comp φ.symm.toEmbedding)
  · refine regular_profile_excludes_all_forms (n := 8064) (d := 3900)
      (constituentGraph_profile H ⟨15625, 7560, 3655, 3660⟩ h root true)
      (by decide) (by decide) (by decide) (by decide) ?_ ?_
    · exact fun hc => (by decide : ¬ CoverDegreeDivisibility 8064 3900)
        (coverDegree_divisibility hc)
    · exact fun hc => (by decide : ¬ CoverDegreeDivisibility 8064 4163)
        (coverDegree_divisibility hc)

end EPPAIII.Primitive
