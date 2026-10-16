import EPPAIII.BlockSystems.RookThreeZeroCrossConclusion
import EPPAIII.BlockSystems.RookThreeEppaCrossDegree

/-!
# The R3 exception: all small uniform cross-degrees

All genuinely delicate local configurations are classified:
degree 0 gives 2R3, degree 1 gives two canonical matching
models, degrees 2 and 3 are impossible by actual EPPA profile
orbit multiplicities, and degree 4 gives two canonical rook
doubles, excluding the other two by triangle-count certificates.

No outside clique partition, coherent EPPA lift, or labelled
outside action is postulated. The one remaining hypothesis is
uniform cross-degree k ≤ 4. Deriving it (up to simultaneous
graph complementation and self-complementarity of R3) from
the manuscript's actual imprimitivity hypotheses is separate.
-/

namespace EPPAIII.BlockSystems

/-- Full graph identification under uniform outside cross-degree
zero through four, preserving the original embedded R3. -/
theorem rook_eppa_small_uniform_cross_degree_classification
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (h18 : Fintype.card W = 18)
    (k : ℕ) (hk : k ≤ 4)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = k) :
    (∃ φ : Bool × rookVertex ≃ W,
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookDisjointDoubleGraph) ∨
    (∃ (φ : Bool × rookVertex ≃ W) (topComplement : Bool),
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookMatchingGraph topComplement) ∨
    (∃ (φ : Bool × rookVertex ≃ W) (crossNonrook : Bool),
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookDoubleGraph false crossNonrook) := by
  classical
  by_cases hZero : k = 0
  · left
    exact rook_eppa_zero_cross_host_is_two_rook_graphs
      H e heppa hTrans h18
      (by intro w hw; simpa [hZero] using hDegree w hw)
  have hOutCard : (finiteOutside e).card = 9 :=
    rook_outside_card_nine e h18
  obtain ⟨w,hw⟩ : (finiteOutside e).Nonempty :=
    Finset.card_pos.mp (by omega)
  by_cases hOne : k = 1
  · right
    left
    exact rook_eppa_singleton_host_two_matching_graphs
      H e heppa hTrans h18 w hw
      (by simpa [hOne] using hDegree w hw)
  by_cases hTwo : k = 2
  · exfalso
    exact rook_eppa_outside_cross_degree_two_impossible
      H e heppa h18
      (by intro z hz; simpa [hTwo] using hDegree z hz)
  by_cases hThree : k = 3
  · exfalso
    exact rook_eppa_outside_cross_degree_three_impossible
      H e heppa h18
      (by intro z hz; simpa [hThree] using hDegree z hz)
  have hFour : k = 4 := by omega
  right
  right
  exact rook_eppa_degree_four_host_is_rook_double
    H e heppa hTrans h18
    (by intro z hz; simpa [hFour] using hDegree z hz)

end EPPAIII.BlockSystems
