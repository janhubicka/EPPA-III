import EPPAIII.BlockSystems.RookThreePairOutsideGraph
import EPPAIII.BlockSystems.CanonicalPairs
import EPPAIII.BlockSystems.GraphTransport

/-!
# R3 outside-graph classification with actual two-point blocks

If each imprimitivity block of an eighteen-vertex EPPA host
has two vertices, and each contains one selected rook vertex,
the canonical pair-equivalence is constructed from the actual
block map. The full rook EPPA action on its mates and equality
of the two half-edge counts then force the outside graph to be
R3 or its complement.

There is no pre-labelled outside action or coherent EPPA choice.
-/

namespace EPPAIII.BlockSystems

/-- The size-two/transversal branch of current Claim 6.16,
giving actual host coordinates that fix the selected R3. -/
theorem rook_eppa_two_point_blocks_outside_graph_two_forms
    {W B : Type*}
    [Fintype W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hInject : Function.Injective (fun x : rookVertex =>
      block (e x)))
    (hTwo : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = 2)
    (h18 : Fintype.card W = 18) :
    ∃ φ : Bool × rookVertex ≃ W,
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      (CliqueCovers.sideGraph (H.comap φ) true = rookThreeGraph ∨
       CliqueCovers.sideGraph (H.comap φ) true = rookThreeGraphᶜ) := by
  classical
  have hDouble : Fintype.card W =
      2 * Fintype.card rookVertex := by
    simpa [rookVertex] using h18
  obtain ⟨φ,hBottom,hPairBlock⟩ :=
    exists_canonical_pair_equiv e block hInject hTwo hDouble
  have hEPPA : IsEPPAEmbedding rookThreeGraph
      (H.comap φ) (DoubleCover.bottomEmbedding rookVertex) := by
    have h :=
      eppa_pullback_bottom rookThreeGraph H e heppa φ hBottom
    change IsEPPAEmbedding rookThreeGraph
      (H.comap φ) (DoubleCover.bottomEmbedding rookVertex) at h
    exact h
  have hPairs : DoubleCover.HasInvariantPairs (H.comap φ) :=
    invariant_pairs_of_pullback
      H e block hBlocks hInject φ hPairBlock
  have hTrans' :
      CliqueCovers.HasTransitiveGraphAutomorphisms (H.comap φ) :=
    CliqueCovers.transitive_comap_equiv H φ hTrans
  exact ⟨φ,hBottom,
    rook_paired_eppa_outside_graph_two_forms
      (H.comap φ) hEPPA hPairs hTrans'⟩

end EPPAIII.BlockSystems
