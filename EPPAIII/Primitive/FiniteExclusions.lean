import EPPAIII.Primitive.Order35Transport
import EPPAIII.Primitive.LocalReduction
import EPPAIII.EPPA.ComplementTransport
import EPPAIII.EPPA.HostRelabel

/-!
# Four finite EPPA search assumptions for the primitive proof

The search statements concern explicit graph models. They are passed as
ordinary propositions. Neither numerical strongly regular parameters nor
family labels imply that an arbitrary graph is one of these models.
-/

namespace EPPAIII.Primitive

/-- No subset having at least half the vertices is EPPA via its inclusion. -/
def NoHalfOrderEPPA {W : Type*} [Finite W] (H : SimpleGraph W) : Prop :=
  2 * maxEppaOrder H < Nat.card W

/-- The four finite negative EPPA checks invoked in the primitive classification.
The order-35 table entry in the manuscript uses the complement of `oSixPlus`. -/
structure OrthogonalSearchChecks : Prop where
  oSixPlus : NoHalfOrderEPPA (orthogonalSixGraph true true)
  noSixMinus : NoHalfOrderEPPA (orthogonalSixGraph false false)
  voSixMinus : NoHalfOrderEPPA (vectorOrthogonalSixGraph false)
  voSixPlus : NoHalfOrderEPPA (vectorOrthogonalSixGraph true)

/-- A failed finite check excludes EPPA for every presentation of the selected
induced subgraph, preserving its actual embedding in the checked host. -/
theorem NoHalfOrderEPPA.not_eppa_embedding {V W : Type*} [Finite V] [Finite W]
    {H : SimpleGraph W} (h : NoHalfOrderEPPA H)
    (G : SimpleGraph V) (e : V ↪ W) (hLarge : Nat.card W ≤ 2 * Nat.card V) :
    ¬ IsEPPAEmbedding G H e := by
  intro heppa
  have hOrder := order_le_maxEppaOrder G H e heppa
  unfold NoHalfOrderEPPA at h
  omega

/-- The finite assumption is exactly universal failure for the induced
subsets of the stated size, expressed without any search implementation. -/
theorem noHalfOrderEPPA_iff {W : Type*} [Finite W] (H : SimpleGraph W) :
    NoHalfOrderEPPA H ↔
      ∀ S : Set W, Nat.card W ≤ 2 * Nat.card S →
        ¬ IsEPPAEmbedding (H.induce S) H (Function.Embedding.subtype S) := by
  constructor
  · intro h S hLarge
    exact h.not_eppa_embedding (H.induce S) _ hLarge
  · intro h
    obtain ⟨S, hCard, heppa⟩ := maxEppaOrder_attained H
    unfold NoHalfOrderEPPA
    by_contra hSmall
    exact h S (by omega) heppa

/-- The calculation is carried out in one orientation of a complementary pair. -/
theorem NoHalfOrderEPPA.compl {W : Type*} [Finite W] {H : SimpleGraph W}
    (h : NoHalfOrderEPPA H) : NoHalfOrderEPPA Hᶜ := by
  obtain ⟨S, hCard, heppa⟩ := maxEppaOrder_attained Hᶜ
  have hBoth := eppa_embedding_complement (Hᶜ.induce S) Hᶜ
    (Function.Embedding.subtype S) heppa
  have hComm : (Hᶜ.induce S)ᶜ = H.induce S := by
    ext a b
    change (a ≠ b ∧ ¬ (a.val ≠ b.val ∧ ¬ H.Adj a.val b.val)) ↔ H.Adj a.val b.val
    constructor
    · rintro ⟨hne, hNot⟩
      by_contra hAdj
      exact hNot ⟨fun hEq => hne (Subtype.ext hEq), hAdj⟩
    · intro hAdj
      exact ⟨fun hEq => H.ne_of_adj hAdj (congrArg Subtype.val hEq),
        fun hNot => hNot.2 hAdj⟩
  rw [hComm, compl_compl] at hBoth
  have hOrder := order_le_maxEppaOrder _ _ _ hBoth
  unfold NoHalfOrderEPPA at *
  omega

/-- Move a maximum EPPA base to an isomorphic host using the
specified host isomorphism on the actual selected embedding. -/
theorem maxEppaOrder_le_of_iso {W X : Type*} [Finite W] [Finite X]
    {H : SimpleGraph W} {K : SimpleGraph X} (φ : H ≃g K) :
    maxEppaOrder H ≤ maxEppaOrder K := by
  obtain ⟨S, hCard, heppa⟩ := maxEppaOrder_attained H
  have hEPPA := eppa_relabel_host (H.induce S) (Function.Embedding.subtype S) heppa φ
  simpa only [hCard] using order_le_maxEppaOrder _ _ _ hEPPA

/-- Move a checked exclusion to an isomorphic host. -/
theorem NoHalfOrderEPPA.of_iso {W X : Type*} [Finite W] [Finite X]
    {H : SimpleGraph W} {K : SimpleGraph X} (h : NoHalfOrderEPPA K)
    (φ : H ≃g K) : NoHalfOrderEPPA H := by
  have hOrder := maxEppaOrder_le_of_iso φ
  have hHostCard : Nat.card W = Nat.card X := Nat.card_congr φ.toEquiv
  unfold NoHalfOrderEPPA at *
  omega

/-- An exclusion transfers from either complementary orientation of the model. -/
theorem NoHalfOrderEPPA.of_iso_or_compl {W X : Type*} [Finite W] [Finite X]
    {H : SimpleGraph W} {K : SimpleGraph X} (h : NoHalfOrderEPPA K)
    (hModel : Nonempty (H ≃g K) ∨ Nonempty (H ≃g Kᶜ)) : NoHalfOrderEPPA H := by
  rcases hModel with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact h.of_iso φ
  · exact h.compl.of_iso φ

/-- The order-35 exclusion applies to the bipartition graph in the
classification, with the orientation supplied by the explicit isomorphism. -/
theorem OrthogonalSearchChecks.equalBipartitionThree
    (h : OrthogonalSearchChecks) : NoHalfOrderEPPA (equalBipartitionGraph 3) :=
  h.oSixPlus.compl.of_iso order35OrthogonalComplementIso.symm

end EPPAIII.Primitive
