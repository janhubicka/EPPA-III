import EPPAIII.Primitive.FixedEmbeddingCases
import EPPAIII.Primitive.RookFourShape
import EPPAIII.Primitive.RookPositiveModels
import EPPAIII.Primitive.RookTwoEdgeCriterion

/-!
# Fixed-embedding classification in the four-by-four rook graph
-/

namespace EPPAIII.Primitive

open RookDensity

private abbrev R4Cell := Fin 4 × Fin 4

private theorem matching_of_oppositeStars {S : Set R4Cell} (T : Finset R4Cell)
    (hST : ∀ x, x ∈ T ↔ x ∈ S) (hOpp : HasOppositeStars T) :
    rookHasMatchingDirection S False := by
  obtain ⟨r, c, hRows, hCols⟩ := hOpp
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hRows
  obtain ⟨s, t, hs, ht, hst⟩ := Finset.one_lt_card_iff.mp hCols
  obtain ⟨hac, ha⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbc, hb⟩ := Finset.mem_erase.mp hb
  obtain ⟨hsr, hs⟩ := Finset.mem_erase.mp hs
  obtain ⟨htr, ht⟩ := Finset.mem_erase.mp ht
  refine ⟨⟨(r, a), (hST _).mp ((mem_row _ _ _).mp ha)⟩,
    ⟨(r, b), (hST _).mp ((mem_row _ _ _).mp hb)⟩,
    ⟨(s, c), (hST _).mp ((mem_transpose _ _ _).mp ((mem_row _ _ _).mp hs))⟩,
    ⟨(t, c), (hST _).mp ((mem_transpose _ _ _).mp ((mem_row _ _ _).mp ht))⟩, ?_, ?_⟩
  · simp [RookInducedMatching, rookGraph, Prod.ext_iff, hab, hst, hsr.symm, htr.symm, hac, hbc]
  · simp [rookSameDirection, hst]

private theorem matching_of_sameStars {S : Set R4Cell} (T : Finset R4Cell)
    (hST : ∀ x, x ∈ T ↔ x ∈ S)
    (hSame : SameOrientation T ∨ SameOrientation (transpose T)) :
    rookHasMatchingDirection S True := by
  have pairs (U : Finset R4Cell) (hU : SameOrientation U) :
      ∃ r s a b c d : Fin 4, r ≠ s ∧ a ≠ b ∧ c ≠ d ∧
        a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
        (r, a) ∈ U ∧ (r, b) ∈ U ∧ (s, c) ∈ U ∧ (s, d) ∈ U := by
    obtain ⟨r, s, hrs, A, B, hA, hB, hCardA, hCardB, hDisjoint⟩ := hU
    obtain ⟨a, b, hab, hAB⟩ := Finset.card_eq_two.mp hCardA
    obtain ⟨c, d, hcd, hCD⟩ := Finset.card_eq_two.mp hCardB
    have ha : a ∈ A := by simp [hAB]
    have hb : b ∈ A := by simp [hAB]
    have hc : c ∈ B := by simp [hCD]
    have hd : d ∈ B := by simp [hCD]
    have hD := Finset.disjoint_left.mp hDisjoint
    refine ⟨r, s, a, b, c, d, hrs, hab, hcd, ?_, ?_, ?_, ?_,
      (mem_row _ _ _).mp (hA ha), (mem_row _ _ _).mp (hA hb), (mem_row _ _ _).mp (hB hc),
      (mem_row _ _ _).mp (hB hd)⟩
    exacts [fun h => hD ha (h.symm ▸ hc), fun h => hD ha (h.symm ▸ hd),
      fun h => hD hb (h.symm ▸ hc), fun h => hD hb (h.symm ▸ hd)]
  rcases hSame with hRow | hCol
  · obtain ⟨r, s, a, b, c, d, hrs, hab, hcd, hac, had, hbc, hbd, ha, hb, hc, hd⟩ := pairs T hRow
    refine ⟨⟨(r, a), (hST _).mp ha⟩, ⟨(r, b), (hST _).mp hb⟩,
      ⟨(s, c), (hST _).mp hc⟩, ⟨(s, d), (hST _).mp hd⟩, ?_, ?_⟩
    · simp [RookInducedMatching, rookGraph, Prod.ext_iff, hrs, hab, hcd, hac, had, hbc, hbd]
    · simp [rookSameDirection]
  · obtain ⟨r, s, a, b, c, d, hrs, hab, hcd, hac, had, hbc, hbd, ha, hb, hc, hd⟩ :=
      pairs (transpose T) hCol
    refine ⟨⟨(a, r), (hST _).mp ((mem_transpose _ _ _).mp ha)⟩,
      ⟨(b, r), (hST _).mp ((mem_transpose _ _ _).mp hb)⟩,
      ⟨(c, s), (hST _).mp ((mem_transpose _ _ _).mp hc)⟩,
      ⟨(d, s), (hST _).mp ((mem_transpose _ _ _).mp hd)⟩, ?_, ?_⟩
    · simp [RookInducedMatching, rookGraph, Prod.ext_iff, hrs, hab, hcd, hac, had, hbc, hbd]
    · simp [rookSameDirection, hab, hcd]

private def rookIso_map (r c : Equiv.Perm (Fin 4)) : rookGraph 4 ≃g rookGraph 4 where
  toEquiv := Equiv.prodCongr r c
  map_rel_iff' := by
    intro a b
    exact (rookGraph_preserves_coordinates r c a b).symm

private def rookIso_swap : rookGraph 4 ≃g rookGraph 4 where
  toEquiv := Equiv.prodComm (Fin 4) (Fin 4)
  map_rel_iff' := by
    intro a b
    exact (rookGraph_transpose_auto a b).symm

private theorem matches_corner (S : Set R4Cell)
    (hCorner : ∃ r c : Fin 4, ∀ x ∈ S, x.1 = r ↔ x.2 = c) :
    MatchesPrimitiveFigure (rookGraph 4) (Function.Embedding.subtype S) (rookGraph 4) rookFourFigures := by
  obtain ⟨r, c, hRC⟩ := hCorner
  let f := rookIso_map (Equiv.swap r 3) (Equiv.swap c 3)
  refine ⟨f, {x | (x.1.val < 3 ∧ x.2.val < 3) ∨ (x.1.val = 3 ∧ x.2.val = 3)},
    by simp [rookFourFigures], ?_⟩
  intro x
  let y := f x.val
  have hr : y.1 = 3 ↔ x.val.1 = r := by
    change Equiv.swap r 3 x.val.1 = 3 ↔ x.val.1 = r
    exact ⟨fun h => (Equiv.swap r 3).injective (h.trans (Equiv.swap_apply_left r 3).symm),
      fun h => h.symm ▸ Equiv.swap_apply_left r 3⟩
  have hc : y.2 = 3 ↔ x.val.2 = c := by
    change Equiv.swap c 3 x.val.2 = 3 ↔ x.val.2 = c
    exact ⟨fun h => (Equiv.swap c 3).injective (h.trans (Equiv.swap_apply_left c 3).symm),
      fun h => h.symm ▸ Equiv.swap_apply_left c 3⟩
  have hEq : y.1.val = 3 ↔ y.2.val = 3 := by
    have h3 (a : Fin 4) : a.val = 3 ↔ a = 3 := by
      change a.val = (3 : Fin 4).val ↔ a = 3
      exact Fin.val_injective.eq_iff
    exact (h3 y.1).trans (hr.trans ((hRC x.val x.property).trans (hc.symm.trans (h3 y.2).symm)))
  change (y.1.val < 3 ∧ y.2.val < 3) ∨ (y.1.val = 3 ∧ y.2.val = 3)
  have h1 := y.1.isLt
  have h2 := y.2.isLt
  omega

private theorem matches_stripe (S : Set R4Cell) (swap : Bool)
    (a b : Fin 4) (hab : a ≠ b)
    (hStripe : ∀ x ∈ S, (if swap then x.1 else x.2) = a ∨
      (if swap then x.1 else x.2) = b) :
    MatchesPrimitiveFigure (rookGraph 4) (Function.Embedding.subtype S) (rookGraph 4) rookFourFigures := by
  let s := Equiv.swap a (0 : Fin 4)
  let p := s.trans (Equiv.swap (s b) 1)
  have hsa : s a = 0 := Equiv.swap_apply_left a 0
  have hsb : s b ≠ 0 := fun h => hab (s.injective (hsa.trans h.symm))
  have hpa : p a = 0 := by
    change (Equiv.swap (s b) 1) (s a) = 0
    rw [hsa, Equiv.swap_apply_of_ne_of_ne (Ne.symm hsb) (by decide : (0 : Fin 4) ≠ 1)]
  have hpb : p b = 1 := Equiv.swap_apply_left (s b) 1
  let f := rookIso_map (Equiv.refl _) p
  let φ := if swap then rookIso_swap.trans f else f
  refine ⟨φ, {x | x.2.val < 2}, by simp [rookFourFigures], ?_⟩
  intro x
  have hΦ : (φ x.val).2 = p (if swap then x.val.1 else x.val.2) := by
    cases swap <;> rfl
  change (φ x.val).2.val < 2
  rw [hΦ]
  rcases hStripe x.val x.property with h | h
  · simpa only [h, hpa] using (by decide : (0 : Fin 4).val < 2)
  · simpa only [h, hpb] using (by decide : (1 : Fin 4).val < 2)

/-- The four-by-four rook host witnesses both displayed maximal selections. -/
theorem rookFourFigures_eppa (S : Set (Fin 4 × Fin 4)) (hS : S ∈ rookFourFigures) :
    IsEPPAEmbedding ((rookGraph 4).induce S) (rookGraph 4) (Function.Embedding.subtype S) := by
  have hCorner : {x : Fin 4 × Fin 4 |
      (x.1.val < 3 ∧ x.2.val < 3) ∨ (x.1.val = 3 ∧ x.2.val = 3)} = rookThreeCorner 4 := by
    ext x
    change ((_ ∧ _) ∨ (_ ∧ _)) ↔ ((_ ∧ _) ∨ (_ ∧ _))
    have hRow := x.1.isLt
    have hCol := x.2.isLt
    omega
  rcases (show S = _ ∨ S = _ from by
    simpa only [rookFourFigures, Set.mem_insert_iff, Set.mem_singleton_iff] using hS) with h | h
  · rw [h, hCorner]
    exact rookThreeCorner_eppa 4
  · rw [h]
    exact rookTwoColumns_eppa 4

/-- The exact canonical classification in the four-by-four rook graph. -/
theorem rookFour_canonicalClassification :
    CanonicalFigureClassification (rookGraph 4) rookFourFigures := by
  classical
  intro S hHalf
  refine ⟨?_, fun hFigure => eppa_of_matchesPrimitiveFigure _ _ _ (fun _ _ => Iff.rfl)
    _ _ hFigure rookFourFigures_eppa⟩
  intro hEppa
  let := Fintype.ofFinite S
  let T := S.toFinset
  have hST (x : R4Cell) : x ∈ T ↔ x ∈ S := Set.mem_toFinset
  have hCard : T.card = Nat.card S := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  have hSize : 8 ≤ T.card := by
    have h : 16 ≤ 2 * Nat.card S := by simpa only [Nat.card_prod, Nat.card_fin] using hHalf
    omega
  have hConflict := (rookGraph_eppa_iff_no_conflicting_matchings S).mp hEppa
  by_cases hOpp : HasOppositeStars T
  · have hNoSame : ¬ (SameOrientation T ∨ SameOrientation (transpose T)) :=
      fun hSame => hConflict ⟨matching_of_sameStars T hST hSame, matching_of_oppositeStars T hST hOpp⟩
    obtain ⟨r, c, hRC⟩ := rookFourCorner_of_noSameStars T hSize
      (fun h => hNoSame (Or.inl h)) (fun h => hNoSame (Or.inr h))
    exact matches_corner S ⟨r, c, fun x hx => hRC x ((hST x).mpr hx)⟩
  · rcases rookFourStripe_of_noOppositeStars T hSize hOpp with ⟨a, b, hab, ht⟩ | ⟨a, b, hab, ht⟩
    · exact matches_stripe S true a b hab (fun x hx => ht x ((hST x).mpr hx))
    · exact matches_stripe S false a b hab (fun x hx => ht x ((hST x).mpr hx))

end EPPAIII.Primitive
