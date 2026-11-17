import EPPAIII.Primitive.PublishedRankThreeCoverage
import EPPAIII.TwoGraphs.AllTransversalEppa

/-! # Assembling both full-action branches of the small-witness classification -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.DoubleCover
open EPPAIII.TwoGraphs
open SimpleGraph

universe u v
attribute [local instance] Classical.propDecidable

/-- A fixed copy of the canonical Taylor double whose bottom is precisely
the chosen embedding. -/
def IsTaylorWitnessCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) : Prop :=
  ∃ φ : Bool × V ≃ W,
    (∀ x, φ (false, x) = e x) ∧ pullbackGraph H φ = taylorPairGraph G

/-- The complementary Taylor alternatives for a noncluster base. -/
def NonclusterTaylorWitnessCases {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) : Prop :=
  ¬ IsClusterGraph G ∧ ¬ IsCoClusterGraph G ∧
    ((IsHomogeneousTwoGraph G ∧ IsTaylorWitnessCopy G H e) ∨
      (IsHomogeneousTwoGraph Gᶜ ∧ IsTaylorWitnessCopy Gᶜ Hᶜ e))

/-- The actual-pair model disjunction. Homogeneous two-graphs describe the
Taylor branch intrinsically; their named model recognition is additional. -/
def SmallWitnessModelCases {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  primitiveCases G H e ∨ ImprimitiveHostModels G H e ∨
    ImprimitiveHostModels Gᶜ Hᶜ e ∨ NonclusterTaylorWitnessCases G H e

private theorem eppa_of_taylor_witness_copy
    {V W : Type*} [Fintype V] (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    [DecidableRel G.Adj]
    (hHomogeneous : IsHomogeneousTwoGraph G) (hModel : IsTaylorWitnessCopy G H e) :
    IsEPPAEmbedding G H e := by
  classical
  have hBottom : taylorTransversalGraph G (fun _ => false) = G := by
    ext x y
    change (x ≠ y ∧ (G.Adj x y ↔ false = false)) ↔ G.Adj x y
    exact ⟨fun h => h.2.mpr rfl, fun h => ⟨h.ne, iff_of_true h rfl⟩⟩
  have hEmbedding : taylorTransversalEmbedding (fun _ : V => false) = bottomEmbedding V := rfl
  have hTaylor : IsEPPAEmbedding G (taylorPairGraph G) (bottomEmbedding V) := by
    simpa only [hBottom, hEmbedding] using
      homogeneous_two_graph_all_transversals_eppa G hHomogeneous (fun _ => false)
  obtain ⟨φ, hFixed, hPullback⟩ := hModel
  let iso : pullbackGraph H φ ≃g H := ⟨φ, Iff.rfl⟩
  have hP : IsEPPAEmbedding G (pullbackGraph H φ) (bottomEmbedding V) := by
    rw [hPullback]
    exact hTaylor
  have hEq : (bottomEmbedding V).trans iso.toEquiv.toEmbedding = e := by
    ext x
    exact hFixed x
  simpa only [hEq] using eppa_relabel_host G (bottomEmbedding V) hP iso

/-- Each of the two canonical Taylor branches witnesses the fixed selected graph. -/
theorem eppa_of_nonclusterTaylorWitnessCases
    {V W : Type*} [Fintype V] (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (h : NonclusterTaylorWitnessCases G H e) : IsEPPAEmbedding G H e := by
  rcases h.2.2 with ⟨hHom, hModel⟩ | ⟨hHom, hModel⟩
  · exact eppa_of_taylor_witness_copy G H e hHom hModel
  · have hEppa := @eppa_of_taylor_witness_copy V W _ Gᶜ Hᶜ e _ hHom hModel
    simpa only [compl_compl] using eppa_embedding_complement Gᶜ Hᶜ e hEppa

private theorem nonclusterTaylorWitnessCases_of_eppa
    {V W B : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (block : W → B)
    (hEPPA : IsEPPAEmbedding G H e) (hG : ¬ IsHomogeneousGraph G)
    (hCluster : ¬ IsClusterGraph G) (hCoCluster : ¬ IsCoClusterGraph G)
    (hModel : ImprimitiveTaylorHostModel G H e block) :
    NonclusterTaylorWitnessCases G H e := by
  classical
  obtain ⟨φ, hBottom, mate, hMate, hInter⟩ := hModel.1
  have hPullEPPA := eppa_pullback_bottom G H e hEPPA φ hBottom
  have hEq := canonical_taylor_eq G (pullbackGraph H φ) hPullEPPA.1 mate hMate hInter
  refine ⟨hCluster, hCoCluster, ?_⟩
  cases mate
  · change pullbackGraph H φ = taylorPairGraph G at hEq
    have hTaylor : IsEPPAEmbedding G (taylorPairGraph G) (bottomEmbedding V) := by
      simpa only [hEq] using hPullEPPA
    exact Or.inl ⟨taylor_eppa_two_graph_homogeneous_all_cases G hTaylor hG, φ, hBottom, hEq⟩
  · change pullbackGraph H φ = (taylorPairGraph Gᶜ)ᶜ at hEq
    have hTaylor : IsEPPAEmbedding Gᶜ (taylorPairGraph Gᶜ) (bottomEmbedding V) := by
      simpa only [hEq, compl_compl] using
        eppa_embedding_complement G (pullbackGraph H φ) (bottomEmbedding V) hPullEPPA
    have hEq' : pullbackGraph Hᶜ φ = taylorPairGraph Gᶜ := by
      have hCompl : pullbackGraph Hᶜ φ = (pullbackGraph H φ)ᶜ := by
        ext x y
        change (φ x ≠ φ y ∧ ¬ H.Adj (φ x) (φ y)) ↔
          (x ≠ y ∧ ¬ H.Adj (φ x) (φ y))
        rw [φ.injective.ne_iff]
      rw [hCompl, hEq, compl_compl]
    exact Or.inr ⟨taylor_eppa_two_graph_homogeneous_all_cases Gᶜ hTaylor
      ((nonhomogeneous_complement_iff G).mp hG), φ, hBottom, hEq'⟩

/-- Necessity for all vertex-transitive finite hosts, preserving the chosen
copy in each model. The primitive branch uses the published recognition and
the stated finite checks. The imprimitive branch uses the actual quotient. -/
theorem smallWitnessModelCases_of_eppa
    (hPublished : PublishedRankThreeGraphCoverage.{v})
    (hRecognize : PrimitiveRecognitionInputs.{u, v})
    (hOrthogonal : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hFinite : PrimitiveFiniteChecks)
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hPair : SmallEPPAPair G H e) : SmallWitnessModelCases G H e := by
  classical
  by_cases hPrim : IsPrimitiveAutAction H
  · exact Or.inl ((primitiveCases_iff_eppa_of_publishedRankThreeCoverage hPublished
      hRecognize hOrthogonal hPaley hFinite G H e hPair.eppa.1
      hPair.halfOrder hPair.transitive hPrim).mpr hPair.eppa)
  by_cases hHom : IsHomogeneousGraph H
  · exact Or.inl (Or.inl (Or.inl hHom))
  obtain ⟨B,hFinB,block,hBlocks,hSurj,hMany,⟨a,b,hab,hne⟩⟩ :=
    exists_invariant_block_map_of_not_primitive H hPrim
  let : Finite B := hFinB
  let : Fintype B := Fintype.ofFinite B
  rw [Nat.card_eq_fintype_card] at hMany
  have hNontrivial : ∃ b₀ : B, 2 ≤ ((Finset.univ : Finset W).filter
      (fun w => block w = b₀)).card :=
    ⟨block b, Finset.one_lt_card_iff.mpr ⟨a,b,by simp [hab],by simp,hne⟩⟩
  have hSize : Fintype.card W ≤ 2 * Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using hPair.halfOrder
  have hHostPositive : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨a⟩
  have hSelected : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨_,hNamed | hNamed | ⟨hG,hC,hCo,hTaylor⟩⟩ :=
    nonhomogeneous_transitive_imprimitive_eppa_with_taylor_base
      G H e hPair.eppa block hBlocks hSurj hPair.transitive hHom hMany hNontrivial
      hSize (hRecognize.gardinerSelected G hSelected)
  · exact Or.inr (Or.inl hNamed)
  · exact Or.inr (Or.inr (Or.inl hNamed))
  · exact Or.inr (Or.inr (Or.inr
      (nonclusterTaylorWitnessCases_of_eppa G H e block hPair.eppa hG hC hCo hTaylor)))

end EPPAIII.Primitive
