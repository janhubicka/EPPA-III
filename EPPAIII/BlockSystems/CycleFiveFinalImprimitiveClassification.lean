import EPPAIII.BlockSystems.CycleFiveSmallCrossConclusion
import EPPAIII.BlockSystems.CycleFiveComplementProfile
import EPPAIII.EPPA.ComplementTransport

/-!
# Full ten-vertex imprimitive C5 classification up to complement

An actual transitive EPPA host of C5 has the complementary half
isomorphic to C5, and hence uniform cross-degree k≤5. If k≤2
the exact small-degree classification yields two disjoint cycles,
the prism or one of two canonical cyclic doubles.

If k≥3, complement both host and selected cycle and reindex the
selected cycle by multiplication by two on Fin 5. EPPA and the
actual invariant host block system survive, while every outside
profile changes size from k to 5-k≤2. Apply the same classification.

This completes the elementary classification of current Lemma 6.12
without external graph classifications or coherent EPPA lifts.
-/

namespace EPPAIII.BlockSystems

/-- Complete actual-host classification in the precise
up-to-complement form of the C5 lemma. -/
theorem cycleFive_eppa_imprimitive_models_up_to_complement
    {W B : Type*}
    [Fintype W] [Fintype B] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (hMany : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card) :
    CycleFiveSmallHostPatterns H e ∨
      CycleFiveSmallHostPatterns Hᶜ
        (EPPAIII.relabelEmbedding e cycleFiveDoubleIndex) := by
  classical
  obtain ⟨k,hk,hDegree⟩ :=
    cycleFive_eppa_actual_uniform_cross_degree
      H e heppa hTrans hTen
  by_cases hSmall : k ≤ 2
  · left
    exact cycleFive_eppa_imprimitive_small_cross_classification
      H e heppa block hBlocks hSurj hTrans
      hTen hMany hNontrivial k hSmall hDegree
  · right
    let e' : (Fin 5) ↪ W :=
      EPPAIII.relabelEmbedding e cycleFiveDoubleIndex
    have hEPPAc :
        IsEPPAEmbedding (SimpleGraph.cycleGraph 5) Hᶜ e' :=
      cycleFive_complement_reindexed_eppa H e heppa
    have hTransc :
        CliqueCovers.HasTransitiveGraphAutomorphisms Hᶜ :=
      transitive_complement H hTrans
    have hBlocksc : InvariantBlockMap Hᶜ block := by
      intro q hq x y
      have hOrig : IsGraphAutomorphism H q := by
        simpa using (graphAutomorphism_complement Hᶜ q hq)
      exact hBlocks q hOrig x y
    have hOutside : finiteOutside e' = finiteOutside e :=
      cycleFive_relabel_outside_eq e
    have hDegreeC : ∀ w : W, w ∈ finiteOutside e' →
        (finiteNeighbourhoodProfile Hᶜ e' w).card = 5 - k := by
      intro w hw
      have hwOld : w ∈ finiteOutside e := by
        rw [hOutside] at hw
        exact hw
      have hSum :=
        cycleFive_complement_reindexed_profile_card_sum_five
          H e w hwOld
      have hOld := hDegree w hwOld
      have hSum' :
          (finiteNeighbourhoodProfile Hᶜ e' w).card + k = 5 := by
        simpa only [hOld] using hSum
      omega
    have hSmallC : 5-k ≤ 2 := by omega
    exact cycleFive_eppa_imprimitive_small_cross_classification
      Hᶜ e' hEPPAc block hBlocksc hSurj hTransc
      hTen hMany hNontrivial (5-k) hSmallC hDegreeC

end EPPAIII.BlockSystems
