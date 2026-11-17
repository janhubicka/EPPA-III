import EPPAIII.Primitive.RookObstruction
import EPPAIII.Primitive.RookThreeHomogeneous
import EPPAIII.Primitive.RookPositiveModels
import EPPAIII.Primitive.FiniteExclusions
import EPPAIII.Primitive.PrimitiveCases

/-!
# Rook bounds in the language of the classification
-/

namespace EPPAIII.Primitive

/-- The maximum EPPA order bound is independent of how the selected
embedding into a square rook graph is presented. -/
theorem maxEppaOrder_rookGraph_le (n : ℕ) :
    maxEppaOrder (rookGraph n) ≤ max (2 * n) (n + 6) := by
  obtain ⟨S, hSize, hEppa⟩ := maxEppaOrder_attained (rookGraph n)
  exact hSize ▸ rookGraph_eppa_card_le S hEppa

/-- The bound needed in the 126-point rank-three case. -/
theorem maxEppaOrder_rookFive_le_eleven : maxEppaOrder (rookGraph 5) ≤ 11 :=
  maxEppaOrder_rookGraph_le 5


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

private theorem rookFiveCorner_card : Nat.card (rookThreeCorner 5) = 11 := by
  letI membership (x : Fin 5 × Fin 5) : Decidable (x ∈ rookThreeCorner 5) :=
    inferInstanceAs (Decidable
      ((x.1.val < 3 ∧ x.2.val < 3) ∨ (3 ≤ x.1.val ∧ x.1.val = x.2.val)))
  let selected := Finset.univ.filter (fun x => x ∈ rookThreeCorner 5)
  have hSelected (x : Fin 5 × Fin 5) : x ∈ selected ↔ x ∈ rookThreeCorner 5 := by
    simp [selected]
  letI := Fintype.ofFinset selected hSelected
  rw [Nat.card_eq_fintype_card, Fintype.card_ofFinset selected hSelected]
  decide

/-- The maximum EPPA order of the five-by-five rook graph is eleven. -/
theorem maxEppaOrder_rookFive_eq_eleven : maxEppaOrder (rookGraph 5) = 11 := by
  apply le_antisymm maxEppaOrder_rookFive_le_eleven
  have hOrder := order_le_maxEppaOrder _ _ _ (rookThreeCorner_eppa 5)
  rwa [rookFiveCorner_card] at hOrder

/-- Every square rook graph of side at least five is excluded. -/
theorem noHalfOrderEPPA_rookGraph (n : ℕ) (hn : 5 ≤ n) :
    NoHalfOrderEPPA (rookGraph n) := by
  apply (noHalfOrderEPPA_iff (rookGraph n)).mpr
  intro S hHalf
  exact rookGraph_not_eppa_half S hn
    (by simpa only [Nat.card_prod, Nat.card_fin] using hHalf)

/-- A half-order EPPA witness lying up to complement in the rook family
uses a rook graph of side at most four. -/
theorem rook_side_le_four_of_eppa {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (hEppa : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (n : ℕ) (hModel : IsModelUpToComplement H (rookGraph n)) : n ≤ 4 := by
  by_contra hLarge
  have hNo := (noHalfOrderEPPA_rookGraph n (by omega)).of_iso_or_compl hModel
  exact hNo.not_eppa_embedding G e hHalf hEppa

private theorem homogeneous_graph_of_iso {W F : Type*} [Finite W]
    {H : SimpleGraph W} {K : SimpleGraph F} (φ : H ≃g K)
    (hHom : DoubleCover.IsHomogeneousGraph K) :
    DoubleCover.IsHomogeneousGraph H := by
  let f := φ.toEquiv.toEmbedding
  have hEppa := eppa_of_homogeneousHost H K f hHom (fun _ _ => φ.map_rel_iff.symm)
  have hBack := eppa_relabel_host H f hEppa φ.symm
  have hId : f.trans φ.symm.toEquiv.toEmbedding = Function.Embedding.refl W := by
    ext x
    exact φ.symm_apply_apply x
  exact (hId ▸ hBack).2

/-- The rook branch of the primitive catalogue. Homogeneity settles
`R₃`, and the orientation obstruction excludes larger side lengths.
The only input is the canonical finite check for `R₄`. -/
theorem primitiveCases_of_rook_model {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hEppa : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (n : ℕ) (hn : 3 ≤ n) (hModel : IsModelUpToComplement H (rookGraph n))
    (hRookFour : CanonicalFigureClassification (rookGraph 4) rookFourFigures) :
    primitiveCases G H e := by
  have hUpper := rook_side_le_four_of_eppa G H e hEppa hHalf n hModel
  by_cases hThree : n = 3
  · subst n
    rcases hModel with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact Or.inl (Or.inl (homogeneous_graph_of_iso φ rookThree_homogeneous))
    · have φ' : Hᶜ ≃g rookGraph 3 := by
        simpa only [compl_compl] using complHostIso φ
      exact Or.inr (Or.inl (homogeneous_graph_of_iso φ' rookThree_homogeneous))
  · have hFour : n = 4 := by omega
    subst n
    rcases hModel with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · have hShape := (canonicalFigureClassification_iff_embedding G H e hEppa.1
        hHalf _ _ φ hRookFour).mp hEppa
      exact Or.inl (Or.inr (Or.inr (Or.inl hShape)))
    · have φ' : Hᶜ ≃g rookGraph 4 := by
        simpa only [compl_compl] using complHostIso φ
      have hCompl := eppa_embedding_complement G H e hEppa
      have hShape := (canonicalFigureClassification_iff_embedding Gᶜ Hᶜ e hCompl.1
        hHalf _ _ φ' hRookFour).mp hCompl
      exact Or.inr (Or.inr (Or.inr (Or.inl hShape)))

end EPPAIII.Primitive
