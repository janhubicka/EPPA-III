import EPPAIII.Primitive.AffineLineCompletion
import EPPAIII.Primitive.AffineMatchingExclusion
import EPPAIII.Primitive.AffineTriangleClusterExclusion
import EPPAIII.Primitive.RankThreeFamilyReductions
import EPPAIII.Primitive.PolarSymplecticFive
import EPPAIII.Primitive.PolarOrderForty
import EPPAIII.Primitive.SmallEllipticExclusion
import EPPAIII.Primitive.SymplecticFourFour
import EPPAIII.Primitive.UnitaryFiveTwoPoint
import EPPAIII.Primitive.UnitaryFourTwoExclusion

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

private theorem listedPrimitiveHost_of_model {V W : Type*} [Finite V]
    {H : SimpleGraph V} {K : SimpleGraph W}
    (hIso : IsModelUpToComplement H K) (hListed : IsListedPrimitiveHost K) :
    IsListedPrimitiveHost H := by
  obtain hHom | ⟨n, hn, hTri⟩ | hRook | hCl | hSch := hListed
  · rcases hIso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact Or.inl (homogeneous_graph_of_iso φ hHom)
    · exact Or.inl (homogeneous_graph_of_iso φ
        ((DoubleCover.homogeneous_complement_iff _).mp hHom))
  · exact Or.inr (Or.inl ⟨n, hn, model_up_to_complement_trans hIso hTri⟩)
  · exact Or.inr (Or.inr (Or.inl (model_up_to_complement_trans hIso hRook)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (model_up_to_complement_trans hIso hCl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (model_up_to_complement_trans hIso hSch))))

/-- The rank-two exclusion uses the local clique union and the stabilizer
bound once the shape test rules out the nonlocal half-order selection. The
unitary point model of order 165 uses the exact clique multiplicities,
and the elliptic point model of order 756 uses a stronger factorial bound. -/
def RankTwoPolarCatalogueModel {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  (∃ Q t : ℕ, RankTwoPolarRange Q t ∧
    H.IsSRGWith ((Q + 1) * (Q * t + 1)) (Q * (t + 1)) (Q - 1) (t + 1) ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion (t + 1) Q)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) < (Q / 2).factorial ^ (t + 1))) ∨
  (H.IsSRGWith 165 36 3 9 ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion 9 4)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤ 165888)) ∨
  (H.IsSRGWith 756 130 4 26 ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion 26 5)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ≤ 78000000)) ∨
  (H.IsSRGWith 85 20 3 5 ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion 5 4)) ∧
    (∀ r u v, u ≠ v → H.Adj r u → H.Adj r v →
      Nat.card (pointwiseGraphStabilizer H {r, u, v}) = if H.Adj u v then 384 else 72)) ∨
  (H.IsSRGWith 156 30 4 6 ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion 6 5)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) = 60000)) ∨
  (H.IsSRGWith 112 30 2 10 ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion 10 3)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ∣ 233280)) ∨
  (H.IsSRGWith 325 68 3 17 ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion 17 4)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) ∣ 12533760)) ∨
  (H.IsSRGWith 40 12 2 4 ∧ OrderFortyPolarLocalCheck H) ∨
  Nonempty (H ≃g UnitaryFourTwo.graph)

/-- Published recognition data for the affine Berlekamp–Van Lint–Seidel graph. -/
def AffineMatchingCatalogueModel {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  H.IsSRGWith 243 22 1 2 ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion 11 2)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) = 15840)

/-- Published recognition data for the affine collinearity graph of (GQ(3,5)). -/
def AffineTriangleClusterCatalogueModel {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  H.IsSRGWith 64 18 2 6 ∧
    (∀ r, Nonempty (localGraph H r ≃g cliqueUnion 6 3)) ∧
    (∀ r, Nat.card (pointwiseGraphStabilizer H {r}) = 2160) ∧
    (∀ r w, H.Adj r w → Nat.card (pointwiseGraphStabilizer H {r, w}) = 120)

/-- A semilinear one-dimensional model and the small connection-set
identifications. Exceptional larger full groups use their own rows. -/
inductive AffineLineCatalogueModel {n : ℕ} (H : SimpleGraph (Fin n)) : Prop
  | model {K F : Type} [Field K] [Field F] [Fintype F] [Algebra K F]
      [FiniteDimensional K F] (J : SimpleGraph F)
      (hModel : IsModelUpToComplement H J)
      (hAffine : HasAffineLineAction K J) {p : ℕ} (hp : p.Prime)
      (hCard : Nat.card F = p ^ Module.finrank K F)
      (hConnection : AffineLineConnection J p (Module.finrank K F))

private theorem affineLineCatalogueModel_listed {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {n : ℕ} {L : SimpleGraph (Fin n)}
    {e : V ↪ W} (hModel : AffineLineCatalogueModel L)
    (hIso : IsModelUpToComplement H L) (hEPPA : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) :
    IsListedPrimitiveHost H := by
  obtain ⟨J, hJ, hAffine, hp, hCard, hConnection⟩ := hModel
  have hModel := model_up_to_complement_trans hIso hJ
  apply listedPrimitiveHost_of_model hModel
  rcases hModel with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact affineLine_listed_of_eppa G J _
      (eppa_relabel_host G e hEPPA φ) ((Nat.card_congr φ.toEquiv).symm.trans_le hHalf)
      hAffine hp hCard hConnection
  · have φ' : Hᶜ ≃g J := by simpa only [compl_compl] using complHostIso φ
    exact affineLine_listed_of_eppa Gᶜ J _
      (eppa_relabel_host Gᶜ e (eppa_embedding_complement G H e hEPPA) φ')
      ((Nat.card_congr φ'.toEquiv).symm.trans_le hHalf) hAffine hp hCard hConnection

/-- A row can use global exclusions, a listed positive host,
or an exclusion that uses the selected constituent sizes. -/
def CompleteRankThreeCase {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  RecognizedRankThreeFamily H ∨ IsListedPrimitiveHost H ∨
    RankTwoPolarCatalogueModel H ∨ AffineMatchingCatalogueModel H ∨
    AffineTriangleClusterCatalogueModel H ∨ AffineLineCatalogueModel H

private theorem rankTwoPolarCatalogueModel_excludes_embedding
    {V W : Type*} [Finite V] {n : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph (Fin n)}
    {e : V ↪ W} {root : V}
    (hModel : RankTwoPolarCatalogueModel K) (φ : H ≃g K)
    (hTrans : HasTransitiveGraphAutomorphisms H) (hEPPA : IsEPPAEmbedding G H e)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (hShapes : ∀ r, SelectedConstituentShapes G H e r) :
    False := by
  classical
  let f := e.trans φ.toEquiv.toEmbedding
  have hMoved := eppa_relabel_host G e hEPPA φ
  have hSize := (Nat.card_congr φ.toEquiv).symm.trans_le hHalf
  have hNonlocal := ((hShapes root).relabel φ).2
  obtain ⟨Q, t, hRange, hSRG, hLocal, hStabilizer⟩ |
      ⟨hSRG, hLocal, hStabilizer⟩ | ⟨hSRG, hLocal, hStabilizer⟩ |
      ⟨hSRG, hLocal, hTriple⟩ | ⟨hSRG, hLocal, hStabilizer⟩ |
      ⟨hSRG, hLocal, hStabilizer⟩ | ⟨hSRG, hLocal, hStabilizer⟩ | ⟨hSRG, hCheck⟩ | ⟨⟨ψ⟩⟩ := hModel
  · obtain ⟨hLocalModel⟩ := hLocal (f root)
    exact polar_rankTwo_not_eppa_of_small_stabilizer G K f hMoved hSize
      (transitive_of_iso φ hTrans) root hRange hSRG hLocalModel hNonlocal (hStabilizer (f root))
  · obtain ⟨hLocalModel⟩ := hLocal (f root)
    exact unitaryFiveTwo_point_not_eppa G K f hMoved hSize root hSRG hLocalModel
      hNonlocal (hStabilizer (f root))
  · obtain ⟨hLocalModel⟩ := hLocal (f root)
    exact ellipticSixFive_not_eppa G K f hMoved hSize
      (transitive_of_iso φ hTrans) root hSRG hLocalModel hNonlocal (hStabilizer (f root))
  · obtain ⟨hLocalModel⟩ := hLocal (f root)
    exact symplecticFourFour_not_eppa G K f hMoved root hSRG hLocalModel
      (hTriple (f root)) hSize hNonlocal
  · obtain ⟨hLocalModel⟩ := hLocal (f root)
    exact symplecticFourFive_not_eppa G K f hMoved hSize
      (transitive_of_iso φ hTrans) root hSRG hLocalModel hNonlocal (hStabilizer (f root))
  · obtain ⟨hLocalModel⟩ := hLocal (f root)
    exact ellipticSixThree_not_eppa G K f hMoved hSize
      (transitive_of_iso φ hTrans) root hSRG hLocalModel hNonlocal (hStabilizer (f root))
  · obtain ⟨hLocalModel⟩ := hLocal (f root)
    exact ellipticSixFour_not_eppa G K f hMoved hSize
      (transitive_of_iso φ hTrans) root hSRG hLocalModel hNonlocal (hStabilizer (f root))
  · exact polarSymplecticThree_not_eppa G K f hMoved hSize hSRG hCheck
      (fun r => ((hShapes r).relabel φ).2)
  · let τ := φ.trans ψ
    exact unitaryFourTwo_not_eppa G (e.trans τ.toEquiv.toEmbedding)
      (eppa_relabel_host G e hEPPA τ) root (transitive_of_iso τ hTrans)
      ((Nat.card_congr τ.toEquiv).symm.trans_le hHalf) ((hShapes root).relabel τ).2

private theorem affineMatchingCatalogueModel_excludes_embedding
    {V W : Type*} [Finite V] {n : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph (Fin n)}
    {e : V ↪ W} {root : V}
    (hModel : AffineMatchingCatalogueModel K) (φ : H ≃g K)
    (hEPPA : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hShape : SelectedConstituentShapes G H e root) :
    False := by
  classical
  let f := e.trans φ.toEquiv.toEmbedding
  have hMoved := eppa_relabel_host G e hEPPA φ
  have hSize := (Nat.card_congr φ.toEquiv).symm.trans_le hHalf
  obtain ⟨hSRG, hLocal, hStabilizer⟩ := hModel
  obtain ⟨hLocalModel⟩ := hLocal (f root)
  exact affine_blvs_not_eppa G K f hMoved root hSRG hLocalModel (hStabilizer (f root))
    hSize (hShape.relabel φ).2

private theorem affineTriangleClusterCatalogueModel_excludes_embedding
    {V W : Type*} [Finite V] {n : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W} {K : SimpleGraph (Fin n)}
    {e : V ↪ W} {root : V}
    (hModel : AffineTriangleClusterCatalogueModel K) (φ : H ≃g K)
    (hEPPA : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hShape : SelectedConstituentShapes G H e root) :
    False := by
  classical
  let f := e.trans φ.toEquiv.toEmbedding
  have hMoved := eppa_relabel_host G e hEPPA φ
  have hSize := (Nat.card_congr φ.toEquiv).symm.trans_le hHalf
  obtain ⟨hSRG, hLocal, hPoint, hPair⟩ := hModel
  obtain ⟨hLocalModel⟩ := hLocal (f root)
  exact affine_gqThreeFive_not_eppa G K f hMoved root hSRG hLocalModel (hPoint (f root))
    (hPair (f root)) hSize (hShape.relabel φ).2

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
    (root : V) (hShapes : ∀ r, SelectedConstituentShapes G H e r) :
    primitiveCases G H e := by
  have hShape := hShapes root
  have hEither := (selected_subconstituent_at_least_half G H e root hRank.2.2.1 hHalf).imp
    hShape.1 hShape.2
  obtain hCases | ⟨c, K, hMem, hIso⟩ :=
    primitiveCases_or_residual_rankThree_model catalog G H e hRank hEPPA hHalf hModel
      hOrthogonal (e root) (fun _ => hEither)
  · exact hCases
  obtain hKnown | hListed | hPolar | hMatching | hTriangle | hLine := hCoverage c K hMem
  · obtain hExclude | hForms := hKnown.exclusion hOrthogonal
    · exact False.elim ((hExclude.of_iso_or_compl hIso).not_eppa_embedding G e hHalf hEPPA)
    · obtain ⟨hLocal, hNonlocal⟩ := constituent_forms_exclusion_of_model hForms hIso (e root)
      exact False.elim (hEither.elim hLocal hNonlocal)
  · have hListed' := listedPrimitiveHost_of_model hIso hListed
    exact (primitiveCases_iff_eppa_of_listedHost G H e hEPPA.1 hHalf hListed' hFinite).mpr hEPPA
  · rcases hIso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact False.elim (rankTwoPolarCatalogueModel_excludes_embedding (root := root)
        hPolar φ hRank.2.2.1 hEPPA hHalf hShapes)
    · have φ' : Hᶜ ≃g K.2 := by simpa only [compl_compl] using complHostIso φ
      exact False.elim (rankTwoPolarCatalogueModel_excludes_embedding hPolar φ'
        (transitive_complement H hRank.2.2.1) (eppa_embedding_complement G H e hEPPA)
        hHalf (fun r => (hShapes r).compl))
  · rcases hIso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact False.elim (affineMatchingCatalogueModel_excludes_embedding
        hMatching φ hEPPA hHalf hShape)
    · have φ' : Hᶜ ≃g K.2 := by simpa only [compl_compl] using complHostIso φ
      exact False.elim (affineMatchingCatalogueModel_excludes_embedding
        hMatching φ' (eppa_embedding_complement G H e hEPPA) hHalf hShape.compl)
  · rcases hIso with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact False.elim (affineTriangleClusterCatalogueModel_excludes_embedding
        hTriangle φ hEPPA hHalf hShape)
    · have φ' : Hᶜ ≃g K.2 := by simpa only [compl_compl] using complHostIso φ
      exact False.elim (affineTriangleClusterCatalogueModel_excludes_embedding
        hTriangle φ' (eppa_embedding_complement G H e hEPPA) hHalf hShape.compl)

  · exact (primitiveCases_iff_eppa_of_listedHost G H e hEPPA.1 hHalf
      (affineLineCatalogueModel_listed hLine hIso hEPPA hHalf) hFinite).mpr hEPPA

end EPPAIII.Primitive
