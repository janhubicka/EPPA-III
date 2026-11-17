import EPPAIII.Primitive.FixedEmbeddingCases
import EPPAIII.Primitive.TriangularObstruction
import EPPAIII.Primitive.ClebschSchlafliModels

/-!
# The primitive cases of the classification theorem

The three finite clauses have concrete labelled hosts and concrete
maximal selections. Their external computational inputs concern those
three finite statements alone. The triangular clause uses the edge set
of the given embedding.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.DoubleCover

universe u v

/-- The homogeneous, triangular, and three finite primitive cases, with
the selected embedding kept in the statement. -/
def orientedPrimitiveCases : PairClassification.{u, v} :=
  fun {_ _} _ H e =>
    IsHomogeneousGraph H ∨ TriangularPair H e ∨
    MatchesPrimitiveFigure H e (rookGraph 4) rookFourFigures ∨
    MatchesPrimitiveFigure H e clebschGraph clebschLargeFigures ∨
    MatchesPrimitiveFigure H e schlafliGraph schlafliLargeFigures

/-- The classification up to simultaneous complementation of the pair. -/
def primitiveCases : PairClassification.{u, v} :=
  complementClosedCases orientedPrimitiveCases

/-- Closed finite recognition obligations. Each can be independently
checked by enumerating the actual host orbits and the extension property. -/
structure PrimitiveFiniteChecks : Prop where
  rookFour : CanonicalFigureClassification (rookGraph 4) rookFourFigures
  clebsch : CanonicalFigureClassification clebschGraph clebschLargeFigures
  schlafli : CanonicalFigureClassification schlafliGraph schlafliLargeFigures

/-- The primitive hosts in the list, before imposing a condition on the
actual selected embedding. -/
def IsListedPrimitiveHost {W : Type*} (H : SimpleGraph W) : Prop :=
  IsHomogeneousGraph H ∨
  (∃ n ≥ 5, IsModelUpToComplement H (triangularModel n)) ∨
  IsModelUpToComplement H (rookGraph 4) ∨
  IsModelUpToComplement H clebschGraph ∨
  IsModelUpToComplement H schlafliGraph

/-- Homogeneity suffices on each actual induced embedding. -/
theorem eppa_of_homogeneousHost {V W : Type*} [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hHomogeneous : IsHomogeneousGraph H) (hInd : IsInducedGraphEmbedding G H e) :
    IsEPPAEmbedding G H e := by
  have hSelf : IsEPPAEmbedding H H (Function.Embedding.refl W) :=
    ⟨fun _ _ => Iff.rfl, hHomogeneous⟩
  simpa only [Function.Embedding.trans_refl] using
    eppa_precompose_induced G H H e (Function.Embedding.refl W) hInd hSelf

/-- The primitive list gives EPPA for the actual embedding. The required
computational inputs are precisely the three named finite checks. -/
theorem eppa_of_primitiveCases {V W : Type*} [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hCheck : PrimitiveFiniteChecks) (hCases : primitiveCases G H e) :
    IsEPPAEmbedding G H e := by
  have oneOrientation (A : SimpleGraph V) (B : SimpleGraph W)
      (hInd' : IsInducedGraphEmbedding A B e) (h : orientedPrimitiveCases A B e) :
      IsEPPAEmbedding A B e := by
    obtain hHom | hTri | hRook | hClebsch | hSchlafli := h
    · exact eppa_of_homogeneousHost A B e hHom hInd'
    · exact eppa_of_triangularPair A B e hInd' hTri
    · obtain ⟨φ, S, hS, hImage⟩ := hRook
      exact (canonicalFigureClassification_iff_embedding A B e hInd' hHalf
        _ _ φ hCheck.rookFour).mpr ⟨φ, S, hS, hImage⟩
    · obtain ⟨φ, S, hS, hImage⟩ := hClebsch
      exact (canonicalFigureClassification_iff_embedding A B e hInd' hHalf
        _ _ φ hCheck.clebsch).mpr ⟨φ, S, hS, hImage⟩
    · obtain ⟨φ, S, hS, hImage⟩ := hSchlafli
      exact (canonicalFigureClassification_iff_embedding A B e hInd' hHalf
        _ _ φ hCheck.schlafli).mpr ⟨φ, S, hS, hImage⟩
  obtain h | h := hCases
  · exact oneOrientation G H hInd h
  · have hCompl := oneOrientation Gᶜ Hᶜ (induced_embedding_complement G H e hInd) h
    simpa only [compl_compl] using eppa_embedding_complement Gᶜ Hᶜ e hCompl

/-- A half-order EPPA embedding into a triangular host identifies the
actual selected edge set as triangle-free. -/
theorem triangularPair_of_eppa {V W : Type*} [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (heppa : IsEPPAEmbedding G H e)
    (n : ℕ) (hn : 5 ≤ n) (φ : H ≃g triangularModel n) :
    TriangularPair H e := by
  classical
  let model := triangularModel n
  let f := e.trans φ.toEquiv.toEmbedding
  let S := Set.range f
  let := Fintype.ofFinite S
  have hSize : Fintype.card (TwoSet (Fin n)) ≤ 2 * Fintype.card S := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_congr φ.toEquiv, ← Nat.card_congr (Equiv.ofInjective f f.injective)]
    exact hHalf
  have hModel := eppa_relabel_host G e heppa φ
  have hSelect := (eppa_iff_induce_range G model f hModel.1).mp hModel
  have hTri := (triangularGraph_eppa_iff_triangleFreeEdges S (by simpa using hn) hSize).mp hSelect
  exact ⟨n, hn, φ, hTri⟩

private def complHostIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := φ.toEquiv
  map_rel_iff' := by
    intro a b
    change (φ a ≠ φ b ∧ ¬ H.Adj (φ a) (φ b)) ↔ (a ≠ b ∧ ¬ G.Adj a b)
    exact and_congr (not_congr φ.injective.eq_iff) (not_congr φ.map_rel_iff)

/-- For each of the listed hosts, the Lean statement keeps both directions
and the actual selected embedding. The remaining necessity obligation of
the primitive theorem is the exhaustion of these host alternatives. -/
theorem primitiveCases_iff_eppa_of_listedHost {V W : Type*} [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hListed : IsListedPrimitiveHost H) (hChecks : PrimitiveFiniteChecks) :
    primitiveCases G H e ↔ IsEPPAEmbedding G H e := by
  refine ⟨eppa_of_primitiveCases G H e hInd hHalf hChecks, ?_⟩
  intro hEppa
  obtain hHom | ⟨n, hn, hTri | hTri⟩ | hRook | hClebsch | hSchlafli := hListed
  · exact Or.inl (Or.inl hHom)
  · obtain ⟨φ⟩ := hTri
    exact Or.inl (Or.inr (Or.inl (triangularPair_of_eppa G H e hHalf hEppa n hn φ)))
  · obtain ⟨φ⟩ := hTri
    have φ' : Hᶜ ≃g triangularModel n := by simpa only [compl_compl] using complHostIso φ
    have h := triangularPair_of_eppa Gᶜ Hᶜ e hHalf
      (eppa_embedding_complement G H e hEppa) n hn φ'
    exact Or.inr (Or.inr (Or.inl h))
  · have hCase : ∀ (A : SimpleGraph V) (B : SimpleGraph W),
        IsEPPAEmbedding A B e → (B ≃g rookGraph 4) → orientedPrimitiveCases A B e :=
      fun A B h φ => Or.inr (Or.inr (Or.inl
        ((canonicalFigureClassification_iff_embedding A B e h.1 hHalf _ _ φ hChecks.rookFour).mp h)))
    obtain hModel | hModel := hRook
    · obtain ⟨φ⟩ := hModel
      exact Or.inl (hCase G H hEppa φ)
    · obtain ⟨φ⟩ := hModel
      exact Or.inr (hCase Gᶜ Hᶜ (eppa_embedding_complement G H e hEppa)
        (by simpa only [compl_compl] using complHostIso φ))
  · have hCase : ∀ (A : SimpleGraph V) (B : SimpleGraph W),
        IsEPPAEmbedding A B e → (B ≃g clebschGraph) → orientedPrimitiveCases A B e :=
      fun A B h φ => Or.inr (Or.inr (Or.inr (Or.inl
        ((canonicalFigureClassification_iff_embedding A B e h.1 hHalf _ _ φ hChecks.clebsch).mp h))))
    obtain hModel | hModel := hClebsch
    · obtain ⟨φ⟩ := hModel
      exact Or.inl (hCase G H hEppa φ)
    · obtain ⟨φ⟩ := hModel
      exact Or.inr (hCase Gᶜ Hᶜ (eppa_embedding_complement G H e hEppa)
        (by simpa only [compl_compl] using complHostIso φ))
  · have hCase : ∀ (A : SimpleGraph V) (B : SimpleGraph W),
        IsEPPAEmbedding A B e → (B ≃g schlafliGraph) → orientedPrimitiveCases A B e :=
      fun A B h φ => Or.inr (Or.inr (Or.inr (Or.inr
        ((canonicalFigureClassification_iff_embedding A B e h.1 hHalf _ _ φ hChecks.schlafli).mp h))))
    obtain hModel | hModel := hSchlafli
    · obtain ⟨φ⟩ := hModel
      exact Or.inl (hCase G H hEppa φ)
    · obtain ⟨φ⟩ := hModel
      exact Or.inr (hCase Gᶜ Hᶜ (eppa_embedding_complement G H e hEppa)
        (by simpa only [compl_compl] using complHostIso φ))

end EPPAIII.Primitive
