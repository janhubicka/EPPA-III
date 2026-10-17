import EPPAIII.BlockSystems.RookThreeOutsideEqualEdges
import EPPAIII.DoubleCover.TwoPointAction
import EPPAIII.EPPA.ProfileAction

/-!
# R3 outside graph in an actual invariant two-point fibre host

If EPPA gives the selected bottom rook graph and all automorphisms
preserve the paired fibres, every rook automorphism has a genuine
host lift sending each outside mate to the corresponding mate.
Hence the outside graph is invariant under all 72 rook automorphisms.

The two vertex-pair orbits give four possible outside graphs.
Vertex-transitivity of H forces its two halves to have equal edge
counts (18); only rook and complementary rook remain.

Unlike previous proofs, this uses neither an outside neighbourhood
profile assumption nor a coherent action of chosen EPPA lifts.
-/

namespace EPPAIII.BlockSystems

/-- Any pair-invariant vertex-transitive EPPA host of the 3x3
rook graph has outside induced graph R3 or its complement. -/
theorem rook_paired_eppa_outside_graph_two_forms
    (H : SimpleGraph (Bool × rookVertex))
    [DecidableRel H.Adj]
    (heppa : IsEPPAEmbedding rookThreeGraph H
      (DoubleCover.bottomEmbedding rookVertex))
    (hPairs : DoubleCover.HasInvariantPairs H)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H) :
    CliqueCovers.sideGraph H true = rookThreeGraph ∨
      CliqueCovers.sideGraph H true = rookThreeGraphᶜ := by
  classical
  let K := CliqueCovers.sideGraph H true
  have hOutsideAction :
      ∀ p : rookAutParameter,
        IsGraphAutomorphism K (rookParameterizedAut p) := by
    intro p
    obtain ⟨q,hq,hCompat⟩ :=
      eppa_lifts_total rookThreeGraph H
        (DoubleCover.bottomEmbedding rookVertex) heppa
        (rookParameterizedAut p)
        (rookParameterizedAut_graph_automorphism p)
    obtain ⟨σ,hσ⟩ := hPairs q hq
    have hBottom (x : rookVertex) :
        q (false,x) = (false,rookParameterizedAut p x) := hCompat x
    have hTop (x : rookVertex) :
        q (true,x) = (true,rookParameterizedAut p x) :=
      DoubleCover.top_image_of_bottom_image q σ hσ
        x (rookParameterizedAut p x) (hBottom x)
    intro x y
    change H.Adj (true,x) (true,y) ↔
      H.Adj (true,rookParameterizedAut p x)
        (true,rookParameterizedAut p y)
    simpa only [hTop x,hTop y] using hq (true,x) (true,y)
  have hFour :
      K = ⊥ ∨ K = rookThreeGraph ∨
        K = rookThreeGraphᶜ ∨ K = ⊤ :=
    rook_invariant_graph_four_forms K hOutsideAction
  have hBottomGraph :
      CliqueCovers.sideGraph H false = rookThreeGraph := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change H.Adj (false,x) (false,y) ↔ rookThreeGraph.Adj x y
    exact (heppa.1 x y).symm
  have hSides : CliqueCovers.sideEdgeCount H false =
      CliqueCovers.sideEdgeCount H true :=
    CliqueCovers.sideEdges_equal_of_transitive_graph H hTrans
  have hTopEdges : K.edgeSet.ncard = 18 := by
    have hCounts :
        (CliqueCovers.sideGraph H false).edgeSet.ncard =
          (CliqueCovers.sideGraph H true).edgeSet.ncard := by
      change (CliqueCovers.sideGraph H false).edgeFinset.card =
        (CliqueCovers.sideGraph H true).edgeFinset.card at hSides
      simpa only [← SimpleGraph.card_edgeSet,
        Set.fintypeCard_eq_ncard] using hSides
    rw [hBottomGraph] at hCounts
    exact hCounts.symm.trans rookThreeGraph_edge_count_eighteen
  rcases hFour with hEmpty | hRook | hComplement | hFull
  · have hZero : K.edgeSet.ncard = 0 := by
      rw [hEmpty]
      simp
    omega
  · exact Or.inl hRook
  · exact Or.inr hComplement
  · have hThirtySix : K.edgeSet.ncard = 36 := by
      rw [hFull]
      exact rookNineComplete_edge_count_thirtysix
    omega

end EPPAIII.BlockSystems
