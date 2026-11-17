import EPPAIII.Primitive.RankThreeFamilyReductions
import EPPAIII.Primitive.PolarRankTwoExclusion

/-! # Catalogue rows that use the selected constituent sizes -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers
open SimpleGraph
attribute [local instance] Classical.propDecidable

/-- At the chosen root, Section 8 gives a shape only on a side where the
selected subgraph covers at least half of the constituent. -/
def SelectedConstituentShapes {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) (e : V ↪ W) (root : V) : Prop :=
  (Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) →
    HasCliqueUnionOrCoverModel (localGraph H (e root))) ∧
  (Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
    HasCliqueUnionOrCoverModel (nonlocalGraph H (e root)))

theorem SelectedConstituentShapes.relabel {V W X : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {K : SimpleGraph X} {e : V ↪ W} {root : V}
    (h : SelectedConstituentShapes G H e root) (φ : H ≃g K) :
    SelectedConstituentShapes G K (e.trans φ.toEquiv.toEmbedding) root := by
  have localMap := localIso φ (e root)
  have nonlocalMap := nonlocalIso φ (e root)
  refine ⟨fun hHalf => model_form_of_iso localMap (h.1 ?_),
    fun hHalf => model_form_of_iso nonlocalMap (h.2 ?_)⟩
  · rw [Nat.card_congr localMap.toEquiv]
    exact hHalf
  · exact (Nat.card_congr nonlocalMap.toEquiv).trans_le hHalf

private theorem model_form_complement {V : Type*} {G : SimpleGraph V}
    (h : HasCliqueUnionOrCoverModel G) : HasCliqueUnionOrCoverModel Gᶜ :=
  model_form_of_compl (G := Gᶜ) (by simpa only [compl_compl] using h)

theorem SelectedConstituentShapes.compl {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {e : V ↪ W} {root : V}
    (h : SelectedConstituentShapes G H e root) : SelectedConstituentShapes Gᶜ Hᶜ e root := by
  have hL := localComplIso H (e root)
  have hN := nonlocalComplIso H (e root)
  refine ⟨fun hHalf => model_form_of_iso hL.symm (model_form_complement (h.2 ?_)),
    fun hHalf => model_form_of_iso hN.symm (model_form_complement (h.1 ?_))⟩
  · exact ((Nat.card_congr hL.toEquiv).symm.trans_le hHalf).trans_eq
      (congrArg (2 * ·) (Nat.card_congr (localComplIso G root).toEquiv))
  · rw [← Nat.card_congr hN.toEquiv, ← Nat.card_congr (nonlocalComplIso G root).toEquiv]
    exact hHalf

private theorem model_up_to_complement_trans {V W X : Type*} {H : SimpleGraph V}
    {K : SimpleGraph W} {L : SimpleGraph X}
    (h : IsModelUpToComplement H K) (k : IsModelUpToComplement K L) :
    IsModelUpToComplement H L := by
  rcases h with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ <;> rcases k with ⟨⟨ψ⟩⟩ | ⟨⟨ψ⟩⟩
  · exact Or.inl ⟨φ.trans ψ⟩
  · exact Or.inr ⟨φ.trans ψ⟩
  · exact Or.inr ⟨φ.trans (complHostIso ψ)⟩
  · exact Or.inl ⟨φ.trans (by simpa only [compl_compl] using complHostIso ψ)⟩

/-- The rank-two exclusion uses the local clique union and the stabilizer
bound once the shape test rules out the nonlocal half-order selection. -/
def RankTwoPolarCatalogueModel {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ Q t : ℕ, RankTwoPolarRange Q t ∧
    H.IsSRGWith ((Q + 1) * (Q * t + 1)) (Q * (t + 1)) (Q - 1) (t + 1) ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion (t + 1) Q)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) < (Q / 2).factorial ^ (t + 1))

/-- A row can use global exclusions, a listed positive host,
or the rank-two argument at the chosen root. -/
def CompleteRankThreeCase {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  RecognizedRankThreeFamily H ∨ IsListedPrimitiveHost H ∨ RankTwoPolarCatalogueModel H

private theorem rankTwoPolarCatalogueModel_excludes_embedding
    {V W : Type*} [Finite V] {n : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph (Fin n)}
    {e : V ↪ W} {root : V}
    (hModel : RankTwoPolarCatalogueModel K) (φ : H ≃g K)
    (hTrans : HasTransitiveGraphAutomorphisms H) (hEPPA : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (hShape : SelectedConstituentShapes G H e root) :
    False := by
  classical
  obtain ⟨Q, t, hRange, hSRG, hLocal, hStabilizer⟩ := hModel
  let f := e.trans φ.toEquiv.toEmbedding
  obtain ⟨hLocalModel⟩ := hLocal (f root)
  exact polar_rankTwo_not_eppa_of_small_stabilizer G K f (eppa_relabel_host G e hEPPA φ)
    ((Nat.card_congr φ.toEquiv).symm.trans_le hHalf) (transitive_of_iso φ hTrans)
    root hRange hSRG hLocalModel (hShape.relabel φ).2 (hStabilizer (f root))

/-- An exhaustive graph catalogue yields the actual primitive case when
each remaining row has the appropriate reduction. -/
theorem primitiveCases_of_completeRankThreeCoverage
    {V W : Type*} [Finite V] [Finite W]
    (catalog : RankThreeCatalog)
    (hCoverage : ∀ c K, K ∈ catalog c → CompleteRankThreeCase K.2)
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hRank : HasRankThreeAutAction H) (hEPPA : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (hModel : InRankThreeCatalog catalog H)
    (hOrthogonal : OrthogonalSearchChecks) (hFinite : PrimitiveFiniteChecks)
    (root : V) (hShape : SelectedConstituentShapes G H e root) :
    primitiveCases G H e := by
  have hEither := (selected_subconstituent_at_least_half G H e root hRank.2.2.1 hHalf).imp
    hShape.1 hShape.2
  obtain hCases | ⟨c, K, hMem, hIso⟩ :=
    primitiveCases_or_residual_rankThree_model catalog G H e hRank hEPPA hHalf hModel
      hOrthogonal (e root) (fun _ => hEither)
  · exact hCases
  obtain hKnown | hListed | hPolar := hCoverage c K hMem
  · obtain hExclude | hForms := hKnown.exclusion hOrthogonal
    · exact False.elim ((hExclude.of_iso_or_compl hIso).not_eppa_embedding G e hHalf hEPPA)
    · obtain ⟨hLocal, hNonlocal⟩ := constituent_forms_exclusion_of_model hForms hIso (e root)
      exact False.elim (hEither.elim hLocal hNonlocal)
  · have hListed' : IsListedPrimitiveHost H := by
      obtain hHom | ⟨n, hn, hTri⟩ | hRook | hCl | hSch := hListed
      · rcases hIso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
        · exact Or.inl (homogeneous_graph_of_iso φ hHom)
        · exact Or.inl (homogeneous_graph_of_iso φ
            ((DoubleCover.homogeneous_complement_iff _).mpr hHom))
      · exact Or.inr (Or.inl ⟨n, hn, model_up_to_complement_trans hIso hTri⟩)
      · exact Or.inr (Or.inr (Or.inl (model_up_to_complement_trans hIso hRook)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (model_up_to_complement_trans hIso hCl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (model_up_to_complement_trans hIso hSch))))
    exact (primitiveCases_iff_eppa_of_listedHost G H e hEPPA.1 hHalf hListed' hFinite).mpr hEPPA
  · rcases hIso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact False.elim (rankTwoPolarCatalogueModel_excludes_embedding
        hPolar φ hRank.2.2.1 hEPPA hHalf hShape)
    · have φ' : Hᶜ ≃g K.2 := by simpa only [compl_compl] using complHostIso φ
      exact False.elim (rankTwoPolarCatalogueModel_excludes_embedding hPolar φ'
        (transitive_complement H hRank.2.2.1) (eppa_embedding_complement G H e hEPPA)
        hHalf hShape.compl)

end EPPAIII.Primitive
