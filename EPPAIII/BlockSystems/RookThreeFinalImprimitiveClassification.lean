import EPPAIII.BlockSystems.RookThreeActualCrossDegree
import EPPAIII.BlockSystems.RookThreeSmallCrossConclusion
import EPPAIII.BlockSystems.RookThreeComplementProfile
import EPPAIII.EPPA.ComplementTransport

/-!
# Complete imprimitive R3 classification up to graph complements

For an actual 18-vertex vertex-transitive, imprimitive EPPA
host of R3, genuine EPPA gives the primitive selected action.
The host blocks have size 2 or 9, and the complementary induced
graph is again R3. Host regularity then gives uniform cross-degree
k, with 0 ≤ k ≤ 9.

If k ≤ 4 the already verified finite profile orbit classification
provides one of the canonical graph models. If k ≥ 5, complement
both host and selected graph, reindex the latter by the explicit
rook self-complementary permutation, and use the exact profile
identity k ↦ 9-k ≤ 4. The complemented host again satisfies genuine
EPPA with an actual selected copy. Apply the same classification.

The graph model alternatives have fixed selected embeddings.
No Gardiner classification, rank-three classification,
abstract outside action, or coherent EPPA extensions are assumed.
-/

namespace EPPAIII.BlockSystems

/-- The three canonical classes of R3 doubles identified by the
small-cross-degree classification. This includes 2R3, the two
matching types, and the two degree-four rook double models. -/
def RookSmallHostPatterns {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W) : Prop :=
    (∃ φ : Bool × rookVertex ≃ W,
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookDisjointDoubleGraph) ∨
    (∃ (φ : Bool × rookVertex ≃ W) (topComplement : Bool),
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookMatchingGraph topComplement) ∨
    (∃ (φ : Bool × rookVertex ≃ W) (crossNonrook : Bool),
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookDoubleGraph false crossNonrook)

/-- This theorem matches the imprimitive R3 classification
of current Lemma 6.14, with the canonical finite graph models
listed explicitly, up to simultaneous graph complementation
and relabelling the selected rook graph. -/
theorem rook_eppa_imprimitive_models_up_to_complement
    {W B : Type*}
    [Fintype W] [Fintype B] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (h18 : Fintype.card W = 18)
    (hMany : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card) :
    RookSmallHostPatterns H e ∨
      RookSmallHostPatterns Hᶜ
        (EPPAIII.relabelEmbedding e rookComplementIndex) := by
  classical
  obtain ⟨k,hk,hDegree⟩ :=
    rook_eppa_imprimitive_uniform_cross_degree
      H e heppa block hBlocks hSurj hTrans
      h18 hMany hNontrivial
  by_cases hSmall : k ≤ 4
  · left
    exact rook_eppa_small_uniform_cross_degree_classification
      H e heppa hTrans h18 k hSmall hDegree
  · right
    let e' : rookVertex ↪ W :=
      EPPAIII.relabelEmbedding e rookComplementIndex
    have hEPPAc : IsEPPAEmbedding rookThreeGraph Hᶜ e' :=
      rook_complement_reindexed_eppa H e heppa
    have hTransc : IsVertexTransitive Hᶜ :=
      transitive_complement H hTrans
    have hOutside :
        finiteOutside e' = finiteOutside e :=
      finiteOutside_relabelEmbedding e rookComplementIndex
    have hDegreeC : ∀ w : W, w ∈ finiteOutside e' →
        (finiteNeighbourhoodProfile Hᶜ e' w).card = 9 - k := by
      intro w hw
      have hwOld : w ∈ finiteOutside e := by
        rw [hOutside] at hw
        exact hw
      have hSum :=
        rook_complement_reindexed_profile_card_sum_nine
          H e w hwOld
      have hOld := hDegree w hwOld
      change (finiteNeighbourhoodProfile Hᶜ e' w).card = 9 - k
      omega
    have hSmallC : 9 - k ≤ 4 := by omega
    exact rook_eppa_small_uniform_cross_degree_classification
      Hᶜ e' hEPPAc hTransc h18
      (9-k) hSmallC hDegreeC

end EPPAIII.BlockSystems
