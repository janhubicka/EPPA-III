import EPPAIII.Primitive.AlternatingFiveArithmetic
import EPPAIII.Primitive.SparseConstituent
import EPPAIII.Primitive.SmallConstituentGraphScreen
import EPPAIII.CliqueCovers.CliqueUnionDegrees

/-! # Exclusion of the alternating forms constituent profiles -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem isomorphic_degree {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (φ : G ≃g H) (v : V) : H.degree (φ v) = G.degree v := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact (Fintype.card_congr (φ.mapNeighborSet v)).symm

/-- At either A(5,q) constituent order and degree, the four classified
host forms are impossible. This conclusion uses only the constituent
profile, so applies equally to any graph with that order and degree. -/
theorem alternatingFive_constituent_exclusion {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {q : Nat} (hq : 2 ≤ q) (side : Bool)
    (hCard : Fintype.card V = ((alternatingFiveParameters q).constituentProfile side).1)
    (hReg : G.IsRegularOfDegree ((alternatingFiveParameters q).constituentProfile side).2) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  let d := ((alternatingFiveParameters q).constituentProfile side).2
  obtain ⟨hDegreePos, hSparse, hOddOrVerySparse⟩ := alternatingFive_constituent_sparse hq side
  obtain ⟨hD, hD1, hD2⟩ := alternatingFive_constituent_near_degree_not_dvd hq side
  change 1 < d at hDegreePos
  change 2 * d + 2 < _ at hSparse
  change _ ∨ 4 * d < _ at hOddOrVerySparse
  change ¬ d ∣ _ at hD
  change ¬ (d + 1) ∣ _ at hD1
  change ¬ (d + 2) ∣ _ at hD2
  change G.IsRegularOfDegree d at hReg
  rw [← hCard] at hSparse hOddOrVerySparse hD hD1 hD2
  have hPos : 0 < Fintype.card V := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t
    refine ⟨fun φ => ?_⟩
    have hModel : 0 < Fintype.card (Fin s × Fin t) := by rw [← φ.card_eq]; exact hPos
    have hOrder : Fintype.card V = s * t := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using φ.card_eq
    obtain ⟨⟨i, a⟩⟩ := Fintype.card_pos_iff.mp hModel
    have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have ht : 0 < t := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have hDeg := isomorphic_degree φ.symm (i, a)
    rw [hReg, CliqueCovers.cliqueUnion_degree hs] at hDeg
    exact hD1 ⟨s, by rw [show d + 1 = t by omega, Nat.mul_comm, hOrder]⟩
  · intro s t
    refine ⟨fun φ => ?_⟩
    have hModel : 0 < Fintype.card (Fin s × Fin t) := by rw [← φ.card_eq]; exact hPos
    have hOrder : Fintype.card V = s * t := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using φ.card_eq
    obtain ⟨⟨i, a⟩⟩ := Fintype.card_pos_iff.mp hModel
    have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hDeg := isomorphic_degree φ.symm (i, a)
    rw [hReg, CliqueCovers.cliqueUnion_compl_regular] at hDeg
    have hBlock : s * t = (s - 1) * t + t := by
      rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ s)]
    by_cases hOne : s = 1
    · subst s
      simp at hDeg
      omega
    · have hLarge : 2 * t ≤ s * t := Nat.mul_le_mul_right t (by omega)
      omega
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    have hOrder := φ.card_eq.trans (coverVertex_card s t)
    have hModel : 0 < Fintype.card (CoverVertex s t) := by rw [← φ.card_eq]; exact hPos
    obtain ⟨⟨_, i, a⟩⟩ := Fintype.card_pos_iff.mp hModel
    have hs : 0 < s := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have ht : 0 < t := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have hDeg := isomorphic_degree φ.symm (left i a)
    rw [hReg, coverGraph_left_degree X Y i a] at hDeg
    cases Y
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hDeg
      have hT : t ∣ Fintype.card V := ⟨2 * s, by rw [hOrder, Nat.mul_comm]⟩
      have hTwoT : 2 * t ∣ Fintype.card V := ⟨s, by rw [hOrder]; ac_rfl⟩
      cases X
      · simp only [coverDiagonalDegree, Nat.add_zero] at hDeg
        exact hD1 (by rwa [show d + 1 = t by omega])
      · simp only [coverDiagonalDegree] at hDeg
        exact hD1 (by rwa [show d + 1 = 2 * t by omega])
      · simp only [coverDiagonalDegree] at hDeg
        exact hD (by rwa [show d = t by omega])
      · simp only [coverDiagonalDegree] at hDeg
        exact hD2 (by rwa [show d + 2 = 2 * t by omega])
    · simp at hDeg
      have hBlock : s * t = (s - 1) * t + t := by
        rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ s)]
      rw [Nat.mul_assoc] at hOrder
      omega
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    have hOrder := φ.card_eq.trans (coverVertex_card s t)
    rcases hOddOrVerySparse with hOdd | hVerySparse
    · have hEven := order_even_of_cover_or_compl G X Y (Or.inr ⟨φ⟩)
      omega
    have hModel : 0 < Fintype.card (CoverVertex s t) := by rw [← φ.card_eq]; exact hPos
    obtain ⟨⟨_, i, a⟩⟩ := Fintype.card_pos_iff.mp hModel
    have hDeg := isomorphic_degree φ.symm (left i a)
    rw [hReg] at hDeg
    have hQuarter := coverGraph_compl_quarter_order_le_degree X Y i a (hDeg ▸ hDegreePos)
    omega

/-- The four classified forms are excluded for either actual constituent
of any strongly regular graph with the A(5,q) parameters. -/
theorem alternatingFive_excludes_actual_constituents {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {q : Nat} (hq : 2 ≤ q)
    (hSRG : let p := alternatingFiveParameters q
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  let G := constituentGraph H root side
  obtain ⟨hCard, hDeg⟩ := constituentGraph_profile H (alternatingFiveParameters q) hSRG root side
  apply alternatingFive_constituent_exclusion G hq side
  · exact Nat.card_eq_fintype_card.symm.trans hCard
  · intro x
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hDeg x

end EPPAIII.Primitive
