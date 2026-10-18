import EPPAIII.BlockSystems.CycleFiveZeroCrossConclusion
import EPPAIII.BlockSystems.CycleFiveActualCrossDegree
import EPPAIII.BlockSystems.CycleFiveMatchingImprimitive
import EPPAIII.BlockSystems.CycleFiveDoubleClassification

/-!
# Complete low-cross-degree imprimitive C5 host models

Given a transitive, imprimitive, ten-vertex EPPA host H of an
induced C5, with common outside cross-degree k≤2, the model
is uniquely constrained as follows:
* k=0: two disjoint cycles;
* k=1: the five-prism matching model (Petersen is primitive);
* k=2: one of two canonical cyclic doubles.

The graph equivalences always fix the designated selected C5.
The main theorem does not assume a pre-labelled outside half,
a prescribed action on it, or coherent EPPA extensions.
-/

namespace EPPAIII.BlockSystems

def CycleFiveSmallHostPatterns {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W) : Prop :=
    (∃ φ : Bool × Fin 5 ≃ W,
      (∀ x : Fin 5, φ (false,x) = e x) ∧
      H.comap φ = cycleFiveDisjointDoubleGraph) ∨
    (∃ φ : Bool × Fin 5 ≃ W,
      (∀ x : Fin 5, φ (false,x) = e x) ∧
      H.comap φ = cycleFiveMatchingGraph false) ∨
    (∃ (φ : Bool × Fin 5 ≃ W) (diagonal : Bool),
      (∀ x : Fin 5, φ (false,x) = e x) ∧
      H.comap φ = cycleFiveDoubleGraph false diagonal)

/-- The exact low-cross-degree half of Lemma 6.12, under actual
imprimitivity rather than an assumed outside-vertex action. -/
theorem cycleFive_eppa_imprimitive_small_cross_classification
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
        (fun w => block w = b₀)).card)
    (k : ℕ) (hk : k ≤ 2)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = k) :
    CycleFiveSmallHostPatterns H e := by
  classical
  by_cases hZero : k = 0
  · left
    exact cycleFive_eppa_zero_cross_host_is_two_cycles
      H e heppa hTrans hTen
      (by intro w hw; simpa [hZero] using hDegree w hw)
  have hOutside : (finiteOutside e).Nonempty := by
    apply Finset.card_pos.mp
    rw [cycleFive_outside_card_five e hTen]
    omega
  obtain ⟨w,hw⟩ := hOutside
  by_cases hOne : k = 1
  · right
    left
    obtain ⟨b₀,hTwo⟩ := hNontrivial
    have hLarge :
        1 < ((Finset.univ : Finset W).filter
          (fun w => block w = b₀)).card := by omega
    obtain ⟨u,hu,v,hv,huv⟩ :=
      Finset.one_lt_card.mp hLarge
    have hSame : block u = block v := by
      have huBlock := (Finset.mem_filter.mp hu).2
      have hvBlock := (Finset.mem_filter.mp hv).2
      exact huBlock.trans hvBlock.symm
    exact cycleFive_eppa_singleton_imprimitive_host_is_prism
      H e heppa hTrans hTen block hBlocks
      hSurj hMany u v huv hSame w hw
      (by simpa [hOne] using hDegree w hw)
  have hTwo : k = 2 := by omega
  right
  right
  exact cycleFive_eppa_degree_two_host_is_cyclic_double
    H e heppa hTrans hTen
    (by intro z hz; simpa [hTwo] using hDegree z hz)

end EPPAIII.BlockSystems
